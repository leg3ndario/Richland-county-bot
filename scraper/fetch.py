#!/usr/bin/env python3
"""
Richland County SC – Motivated Seller Lead Scraper
====================================================
Targets: Richland County Register of Deeds (iDoc portal)
         Richland County Assessor parcel data (ArcGIS REST)
Output:  dashboard/records.json  +  data/records.json
         data/leads_ghl_export.csv
"""

import asyncio
import csv
import json
import os
import re
import sys
import time
import traceback
import zipfile
from datetime import datetime, timedelta, timezone
from io import BytesIO
from pathlib import Path

import requests
from bs4 import BeautifulSoup
from playwright.async_api import async_playwright, TimeoutError as PWTimeout

# ── Optional DBF support (parcel fallback) ────────────────────────────────────
try:
    from dbfread import DBF
    HAS_DBFREAD = True
except ImportError:
    HAS_DBFREAD = False

# ══════════════════════════════════════════════════════════════════════════════
# CONFIG
# ══════════════════════════════════════════════════════════════════════════════

LOOKBACK_DAYS   = int(os.getenv("LOOKBACK_DAYS", "7"))
COUNTY          = "Richland"
STATE           = "SC"

# Richland County Register of Deeds – iDoc public search portal
ROD_BASE        = "https://rod.richlandcountysc.gov"
ROD_SEARCH_URL  = f"{ROD_BASE}/RodPublic/SearchForms/DocumentTypeSearch.aspx"
ROD_DOC_BASE    = f"{ROD_BASE}/RodPublic/SearchResults/DocumentSearch.aspx"

# ArcGIS REST endpoint for Richland County parcels (public FeatureServer)
ARCGIS_PARCEL_URL = (
    "https://services1.arcgis.com/YkiDNd5aIbTOILfR/arcgis/rest/services"
    "/Richland_County_Parcels/FeatureServer/0/query"
)
# Fallback: Richland County open data / GIS hub
ARCGIS_ALT_URL = (
    "https://richlandmaps.com/arcgis/rest/services/Parcels/Parcels/MapServer/0/query"
)

# Output paths (relative to repo root — two levels up from scraper/)
SCRIPT_DIR   = Path(__file__).parent
REPO_ROOT    = SCRIPT_DIR.parent
OUTPUT_PATHS = [
    REPO_ROOT / "dashboard" / "records.json",
    REPO_ROOT / "data"      / "records.json",
]
CSV_PATH = REPO_ROOT / "data" / "leads_ghl_export.csv"

# Document type codes → (category, label)
DOC_TYPE_MAP = {
    "LP":       ("preforeclosure", "Lis Pendens"),
    "NOFC":     ("preforeclosure", "Notice of Foreclosure"),
    "TAXDEED":  ("tax",            "Tax Deed"),
    "JUD":      ("judgment",       "Judgment"),
    "CCJ":      ("judgment",       "Certified Judgment"),
    "DRJUD":    ("judgment",       "Domestic Judgment"),
    "LNCORPTX": ("tax_lien",       "Corp Tax Lien"),
    "LNIRS":    ("tax_lien",       "IRS Lien"),
    "LNFED":    ("tax_lien",       "Federal Lien"),
    "LN":       ("lien",           "Lien"),
    "LNMECH":   ("lien",           "Mechanic Lien"),
    "LNHOA":    ("lien",           "HOA Lien"),
    "MEDLN":    ("lien",           "Medicaid Lien"),
    "PRO":      ("probate",        "Probate Document"),
    "NOC":      ("construction",   "Notice of Commencement"),
    "RELLP":    ("release",        "Release Lis Pendens"),
}

RETRY_ATTEMPTS = 3
RETRY_DELAY    = 3   # seconds between retries
PAGE_TIMEOUT   = 30_000  # ms

# ══════════════════════════════════════════════════════════════════════════════
# UTILITIES
# ══════════════════════════════════════════════════════════════════════════════

def log(msg: str):
    ts = datetime.now(timezone.utc).strftime("%H:%M:%S")
    print(f"[{ts}] {msg}", flush=True)


def safe(fn, default=None):
    """Call fn(); return default on any exception."""
    try:
        return fn()
    except Exception:
        return default


def retry_request(fn, attempts=RETRY_ATTEMPTS, delay=RETRY_DELAY):
    """Retry a callable up to `attempts` times."""
    last_err = None
    for i in range(attempts):
        try:
            return fn()
        except Exception as e:
            last_err = e
            if i < attempts - 1:
                log(f"  ↻ Retry {i+1}/{attempts-1}: {e}")
                time.sleep(delay)
    raise last_err


def parse_amount(text: str) -> float | None:
    if not text:
        return None
    cleaned = re.sub(r"[^\d.]", "", text)
    try:
        return float(cleaned) if cleaned else None
    except ValueError:
        return None


def name_variants(full_name: str) -> list[str]:
    """Return FIRST LAST, LAST FIRST, LAST, FIRST variants."""
    if not full_name:
        return []
    full_name = full_name.strip()
    parts = full_name.split()
    variants = {full_name.upper()}
    if len(parts) >= 2:
        last, first = parts[-1], " ".join(parts[:-1])
        variants.add(f"{last} {first}".upper())
        variants.add(f"{last}, {first}".upper())
    return list(variants)


def week_ago() -> str:
    return (datetime.now(timezone.utc) - timedelta(days=LOOKBACK_DAYS)).strftime("%m/%d/%Y")


def today_str() -> str:
    return datetime.now(timezone.utc).strftime("%m/%d/%Y")

# ══════════════════════════════════════════════════════════════════════════════
# SCORER
# ══════════════════════════════════════════════════════════════════════════════

def compute_flags_and_score(rec: dict) -> tuple[list[str], int]:
    """Derive motivational flags and score (0-100) from a record."""
    flags = []
    cat   = rec.get("cat", "")
    dtype = rec.get("doc_type", "")
    amt   = rec.get("amount")
    owner = rec.get("owner", "").upper()
    filed = rec.get("filed", "")

    if cat == "preforeclosure" or dtype in ("LP", "NOFC"):
        if dtype == "LP":
            flags.append("Lis pendens")
        flags.append("Pre-foreclosure")

    if cat == "judgment":
        flags.append("Judgment lien")

    if cat == "tax_lien" or dtype == "TAXDEED":
        flags.append("Tax lien")

    if dtype in ("LNMECH", "LN", "LNHOA", "MEDLN"):
        flags.append("Mechanic lien")

    if cat == "probate":
        flags.append("Probate / estate")

    # LLC / Corp owner detection
    corp_keywords = ["LLC", "INC", "CORP", "L.L.C", "LTD", "TRUST", "ESTATE",
                     "HOLDINGS", "PROPERTIES", "GROUP", "PARTNERS"]
    if any(kw in owner for kw in corp_keywords):
        flags.append("LLC / corp owner")

    # New this week
    try:
        filed_dt = datetime.strptime(filed, "%m/%d/%Y")
        cutoff   = datetime.now() - timedelta(days=7)
        if filed_dt >= cutoff:
            flags.append("New this week")
    except Exception:
        pass

    # ── Scoring ──────────────────────────────────────────────────────────────
    score = 30  # base

    score += 10 * len(flags)

    # LP + FC combo bonus
    if "Lis pendens" in flags and "Pre-foreclosure" in flags:
        score += 20

    if amt is not None:
        if amt > 100_000:
            score += 15
        elif amt > 50_000:
            score += 10

    if "New this week" in flags:
        score += 5

    has_addr = bool(rec.get("prop_address") or rec.get("mail_address"))
    if has_addr:
        score += 5

    score = min(score, 100)
    return flags, score

# ══════════════════════════════════════════════════════════════════════════════
# PARCEL LOOKUP  (ArcGIS REST → owner name lookup)
# ══════════════════════════════════════════════════════════════════════════════

class ParcelLookup:
    """
    Fetches parcel data from Richland County ArcGIS REST FeatureServer.
    Falls back to downloading a DBF file if the REST call fails.
    Caches all records in-memory keyed by owner-name variants.
    """

    def __init__(self):
        self.by_name:  dict[str, dict] = {}   # "LAST FIRST" → parcel
        self.by_pin:   dict[str, dict] = {}   # parcel id → parcel
        self._loaded = False

    # ── Field normalizer ──────────────────────────────────────────────────────

    @staticmethod
    def _norm(raw: dict) -> dict:
        """Normalize ArcGIS or DBF field names to a standard schema."""
        def g(*keys):
            for k in keys:
                v = raw.get(k) or raw.get(k.upper()) or raw.get(k.lower())
                if v and str(v).strip() not in ("", "None", "NULL"):
                    return str(v).strip()
            return ""

        return {
            "pin":          g("PIN", "PARCEL_ID", "TaxParcelNumber", "OBJECTID"),
            "owner":        g("OWNER", "OWN1", "OwnerName", "OWNER_NAME", "OWN_NAME"),
            "site_addr":    g("SITE_ADDR", "SITEADDR", "SiteAddress", "SITE_ADDRESS",
                              "PropAddress", "PROP_ADDR"),
            "site_city":    g("SITE_CITY", "SiteCity", "PROP_CITY"),
            "site_zip":     g("SITE_ZIP",  "SiteZip",  "PROP_ZIP"),
            "mail_addr":    g("ADDR_1", "MAILADR1", "MailAddress", "MAIL_ADDR",
                              "MAILING_ADDRESS"),
            "mail_city":    g("CITY", "MAILCITY", "MailCity", "MAIL_CITY"),
            "mail_state":   g("STATE", "MAILSTATE", "MailState", "MAIL_STATE"),
            "mail_zip":     g("ZIP",  "MAILZIP",  "MailZip",  "MAIL_ZIP"),
        }

    # ── ArcGIS REST loader ────────────────────────────────────────────────────

    def _fetch_arcgis(self, url: str) -> list[dict]:
        """Page through an ArcGIS FeatureServer layer and return all features."""
        records = []
        offset  = 0
        page_sz = 1000
        while True:
            params = {
                "where":         "1=1",
                "outFields":     "*",
                "f":             "json",
                "resultOffset":  offset,
                "resultRecordCount": page_sz,
                "returnGeometry": "false",
            }
            resp = retry_request(lambda: requests.get(url, params=params, timeout=30))
            data = resp.json()

            if "error" in data:
                raise RuntimeError(f"ArcGIS error: {data['error']}")

            feats = data.get("features", [])
            if not feats:
                break
            for f in feats:
                records.append(f.get("attributes", {}))
            if not data.get("exceededTransferLimit"):
                break
            offset += page_sz
            time.sleep(0.2)

        return records

    # ── DBF fallback loader ───────────────────────────────────────────────────

    def _fetch_dbf_fallback(self) -> list[dict]:
        """
        Try to download the Richland County assessor bulk export (DBF format).
        The county does not expose a direct public bulk DBF URL; this attempts
        the known pattern and gracefully returns [] on failure.
        """
        candidate_urls = [
            # Richland County open data portal – parcel export (DBF inside ZIP)
            "https://www.richlandcountysc.gov/Portals/0/GIS/Parcels.zip",
            "https://opendata.richlandcountysc.gov/datasets/parcels/download",
            "https://richlandmaps.com/data/Parcels.zip",
        ]
        for url in candidate_urls:
            try:
                log(f"  DBF fallback: trying {url}")
                resp = requests.get(url, timeout=30)
                if resp.status_code != 200:
                    continue
                z = zipfile.ZipFile(BytesIO(resp.content))
                dbf_names = [n for n in z.namelist() if n.lower().endswith(".dbf")]
                if not dbf_names:
                    continue
                if not HAS_DBFREAD:
                    log("  dbfread not installed – skipping DBF parse")
                    return []
                raw_bytes = z.read(dbf_names[0])
                tmp = Path("/tmp/parcels.dbf")
                tmp.write_bytes(raw_bytes)
                table = DBF(str(tmp), load=True, ignore_missing_memofile=True)
                return [dict(row) for row in table]
            except Exception as e:
                log(f"  DBF fallback failed for {url}: {e}")
        return []

    # ── Public load ───────────────────────────────────────────────────────────

    def load(self):
        if self._loaded:
            return

        raw_records = []

        # 1. Try primary ArcGIS endpoint
        for url in (ARCGIS_PARCEL_URL, ARCGIS_ALT_URL):
            try:
                log(f"Loading parcels from ArcGIS: {url}")
                raw_records = self._fetch_arcgis(url)
                if raw_records:
                    log(f"  ✓ Loaded {len(raw_records):,} parcels")
                    break
            except Exception as e:
                log(f"  ArcGIS endpoint failed ({url}): {e}")

        # 2. DBF fallback
        if not raw_records:
            log("Trying DBF bulk download fallback …")
            raw_records = self._fetch_dbf_fallback()
            if raw_records:
                log(f"  ✓ Loaded {len(raw_records):,} parcel records from DBF")

        if not raw_records:
            log("  ⚠ No parcel data available – address enrichment disabled")
            self._loaded = True
            return

        for raw in raw_records:
            try:
                p = self._norm(raw)
                if p["pin"]:
                    self.by_pin[p["pin"].upper()] = p
                if p["owner"]:
                    for variant in name_variants(p["owner"]):
                        if variant not in self.by_name:
                            self.by_name[variant] = p
            except Exception:
                pass

        self._loaded = True
        log(f"  Parcel index: {len(self.by_name):,} name variants / "
            f"{len(self.by_pin):,} PINs")

    def lookup(self, owner_name: str) -> dict | None:
        if not self._loaded:
            self.load()
        for v in name_variants(owner_name):
            p = self.by_name.get(v)
            if p:
                return p
        return None

# ══════════════════════════════════════════════════════════════════════════════
# ROD SCRAPER  (Playwright – iDoc ASP.NET portal)
# ══════════════════════════════════════════════════════════════════════════════

async def scrape_rod_doc_type(page, doc_type: str, date_from: str, date_to: str) -> list[dict]:
    """
    Search Richland County ROD for one document type within the date range.
    Returns a list of raw record dicts.
    """
    records = []

    for attempt in range(RETRY_ATTEMPTS):
        try:
            # Navigate to the document-type search page
            await page.goto(ROD_SEARCH_URL, timeout=PAGE_TIMEOUT,
                            wait_until="domcontentloaded")
            await page.wait_for_load_state("networkidle", timeout=PAGE_TIMEOUT)

            # ── Fill in the search form ──────────────────────────────────────
            # Document type dropdown / text field
            doc_type_sel = (
                'select[name*="DocType"], select[id*="DocType"], '
                'input[name*="DocType"], input[id*="DocType"]'
            )
            el = await page.query_selector(doc_type_sel)
            if el:
                tag = await el.get_attribute("tagName") or await el.evaluate("el=>el.tagName")
                if "SELECT" in tag.upper():
                    await el.select_option(value=doc_type)
                else:
                    await el.fill(doc_type)

            # Date From
            date_from_sel = (
                'input[name*="DateFrom"], input[id*="DateFrom"], '
                'input[name*="FromDate"], input[id*="FromDate"], '
                'input[name*="BeginDate"], input[id*="BeginDate"]'
            )
            date_from_el = await page.query_selector(date_from_sel)
            if date_from_el:
                await date_from_el.fill(date_from)

            # Date To
            date_to_sel = (
                'input[name*="DateTo"], input[id*="DateTo"], '
                'input[name*="ToDate"],   input[id*="ToDate"], '
                'input[name*="EndDate"],  input[id*="EndDate"]'
            )
            date_to_el = await page.query_selector(date_to_sel)
            if date_to_el:
                await date_to_el.fill(date_to)

            # Submit
            submit_sel = (
                'input[type="submit"], button[type="submit"], '
                'input[value*="Search"], button:text("Search")'
            )
            await page.click(submit_sel, timeout=10_000)
            await page.wait_for_load_state("networkidle", timeout=PAGE_TIMEOUT)

            # ── Parse results pages ──────────────────────────────────────────
            while True:
                html   = await page.content()
                soup   = BeautifulSoup(html, "lxml")
                page_records = _parse_rod_results_page(soup, doc_type)
                records.extend(page_records)

                # Try "Next" pagination
                next_btn = await page.query_selector(
                    'a:text("Next"), input[value="Next >"], '
                    'a[id*="Next"], a[href*="Page="]'
                )
                if not next_btn:
                    break

                try:
                    href = await next_btn.get_attribute("href") or ""
                    if "__doPostBack" in href:
                        event_target = re.search(r"'([^']+)'", href)
                        if event_target:
                            await page.evaluate(
                                f"__doPostBack('{event_target.group(1)}', '')"
                            )
                            await page.wait_for_load_state("networkidle",
                                                            timeout=PAGE_TIMEOUT)
                    else:
                        await next_btn.click(timeout=10_000)
                        await page.wait_for_load_state("networkidle",
                                                        timeout=PAGE_TIMEOUT)
                except PWTimeout:
                    break

            log(f"  {doc_type}: {len(page_records)} results on last page, "
                f"{len(records)} total")
            break  # success – exit retry loop

        except Exception as e:
            log(f"  ⚠ {doc_type} attempt {attempt+1}: {e}")
            if attempt < RETRY_ATTEMPTS - 1:
                await asyncio.sleep(RETRY_DELAY)
            else:
                log(f"  ✗ {doc_type}: all retries exhausted")

    return records


def _parse_rod_results_page(soup: BeautifulSoup, doc_type: str) -> list[dict]:
    """Parse a single results page from the ROD iDoc portal."""
    records = []

    # Results are typically in a <table> with rows of document data
    tables = soup.find_all("table")
    for table in tables:
        rows = table.find_all("tr")
        # Skip tables with fewer than 2 rows (likely nav / header only)
        if len(rows) < 2:
            continue

        # Detect header row
        headers = []
        hrow = rows[0]
        for th in hrow.find_all(["th", "td"]):
            headers.append(th.get_text(strip=True).lower())

        if not any(k in " ".join(headers) for k in
                   ["doc", "book", "filed", "grantor", "instrument", "record"]):
            continue

        # Map column positions
        col = {h: i for i, h in enumerate(headers)}

        def c(*keys):
            for k in keys:
                for h, i in col.items():
                    if k in h:
                        return i
            return None

        ci_doc_num  = c("instrument", "doc #", "doc num", "book", "id")
        ci_dtype    = c("doc type", "type")
        ci_filed    = c("filed", "record date", "date")
        ci_grantor  = c("grantor", "owner", "seller")
        ci_grantee  = c("grantee", "buyer")
        ci_legal    = c("legal", "description")
        ci_amount   = c("amount", "consideration", "value")

        for row in rows[1:]:
            cells = row.find_all(["td", "th"])
            if not cells:
                continue

            def cell_text(idx):
                if idx is None or idx >= len(cells):
                    return ""
                return cells[idx].get_text(strip=True)

            def cell_link(idx):
                if idx is None or idx >= len(cells):
                    return ""
                a = cells[idx].find("a")
                if a and a.get("href"):
                    href = a["href"]
                    return href if href.startswith("http") else ROD_BASE + "/" + href.lstrip("/")
                return ""

            doc_num   = cell_text(ci_doc_num)
            filed_raw = cell_text(ci_filed)
            grantor   = cell_text(ci_grantor)
            grantee   = cell_text(ci_grantee)
            legal     = cell_text(ci_legal)
            amt_raw   = cell_text(ci_amount)
            dtype_raw = cell_text(ci_dtype) or doc_type
            doc_url   = cell_link(ci_doc_num) or cell_link(0)

            # Skip empty rows
            if not doc_num and not grantor:
                continue

            amount = parse_amount(amt_raw)
            cat, cat_label = DOC_TYPE_MAP.get(doc_type, ("other", dtype_raw))

            # Normalise date
            filed = ""
            for fmt in ("%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y", "%m/%d/%y"):
                try:
                    filed = datetime.strptime(filed_raw, fmt).strftime("%m/%d/%Y")
                    break
                except ValueError:
                    pass
            if not filed:
                filed = filed_raw  # keep raw if unparseable

            records.append({
                "doc_num":   doc_num,
                "doc_type":  doc_type,
                "filed":     filed,
                "cat":       cat,
                "cat_label": cat_label,
                "owner":     grantor,
                "grantee":   grantee,
                "amount":    amount,
                "legal":     legal,
                "clerk_url": doc_url or f"{ROD_BASE}/",
                # parcel fields filled in later
                "prop_address": "",
                "prop_city":    "",
                "prop_state":   STATE,
                "prop_zip":     "",
                "mail_address": "",
                "mail_city":    "",
                "mail_state":   STATE,
                "mail_zip":     "",
                "flags":        [],
                "score":        0,
            })

    return records


async def scrape_all_doc_types(date_from: str, date_to: str) -> list[dict]:
    """Launch Playwright, iterate all document types, return combined records."""
    all_records: list[dict] = []

    async with async_playwright() as pw:
        browser = await pw.chromium.launch(headless=True)
        ctx     = await browser.new_context(
            user_agent=(
                "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
            )
        )
        page = await ctx.new_page()

        # Accept disclaimer if present
        try:
            await page.goto(ROD_BASE, timeout=PAGE_TIMEOUT,
                            wait_until="domcontentloaded")
            agree = await page.query_selector(
                'input[value*="Agree"], button:text("Agree"), '
                'a:text("Agree"), input[value*="Accept"]'
            )
            if agree:
                await agree.click()
                await page.wait_for_load_state("networkidle", timeout=PAGE_TIMEOUT)
        except Exception as e:
            log(f"  Disclaimer page: {e}")

        for doc_type in DOC_TYPE_MAP:
            log(f"Scraping doc type: {doc_type} …")
            recs = await scrape_rod_doc_type(page, doc_type, date_from, date_to)
            all_records.extend(recs)

        await browser.close()

    return all_records

# ══════════════════════════════════════════════════════════════════════════════
# ENRICHMENT  (add parcel address data)
# ══════════════════════════════════════════════════════════════════════════════

def enrich_records(records: list[dict], parcels: ParcelLookup) -> list[dict]:
    enriched = 0
    for rec in records:
        try:
            p = parcels.lookup(rec.get("owner", ""))
            if p:
                rec["prop_address"] = p.get("site_addr", "")
                rec["prop_city"]    = p.get("site_city", "Columbia")
                rec["prop_state"]   = STATE
                rec["prop_zip"]     = p.get("site_zip", "")
                rec["mail_address"] = p.get("mail_addr", "")
                rec["mail_city"]    = p.get("mail_city", "")
                rec["mail_state"]   = p.get("mail_state", STATE)
                rec["mail_zip"]     = p.get("mail_zip", "")
                enriched += 1
        except Exception:
            pass

        # Score after enrichment (has_address check benefits from parcel data)
        try:
            flags, score  = compute_flags_and_score(rec)
            rec["flags"]  = flags
            rec["score"]  = score
        except Exception:
            rec["flags"]  = []
            rec["score"]  = 30

    log(f"Enriched {enriched}/{len(records)} records with parcel address data")
    return records

# ══════════════════════════════════════════════════════════════════════════════
# OUTPUT WRITERS
# ══════════════════════════════════════════════════════════════════════════════

def write_json(records: list[dict], date_from: str, date_to: str):
    with_addr = sum(1 for r in records if r.get("prop_address") or r.get("mail_address"))
    payload = {
        "fetched_at":  datetime.now(timezone.utc).isoformat(),
        "source":      f"Richland County SC Register of Deeds – {ROD_BASE}",
        "date_range":  {"from": date_from, "to": date_to},
        "total":       len(records),
        "with_address": with_addr,
        "records":     records,
    }
    for path in OUTPUT_PATHS:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, indent=2, default=str))
        log(f"  ✓ Wrote {path}")


def write_ghl_csv(records: list[dict]):
    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "First Name", "Last Name",
        "Mailing Address", "Mailing City", "Mailing State", "Mailing Zip",
        "Property Address", "Property City", "Property State", "Property Zip",
        "Lead Type", "Document Type", "Date Filed", "Document Number",
        "Amount/Debt Owed", "Seller Score", "Motivated Seller Flags",
        "Source", "Public Records URL",
    ]
    rows = []
    for rec in records:
        owner = rec.get("owner", "")
        parts = owner.split()
        first = parts[0] if parts else ""
        last  = " ".join(parts[1:]) if len(parts) > 1 else ""

        rows.append({
            "First Name":             first,
            "Last Name":              last,
            "Mailing Address":        rec.get("mail_address", ""),
            "Mailing City":           rec.get("mail_city", ""),
            "Mailing State":          rec.get("mail_state", STATE),
            "Mailing Zip":            rec.get("mail_zip", ""),
            "Property Address":       rec.get("prop_address", ""),
            "Property City":          rec.get("prop_city", ""),
            "Property State":         rec.get("prop_state", STATE),
            "Property Zip":           rec.get("prop_zip", ""),
            "Lead Type":              rec.get("cat_label", ""),
            "Document Type":          rec.get("doc_type", ""),
            "Date Filed":             rec.get("filed", ""),
            "Document Number":        rec.get("doc_num", ""),
            "Amount/Debt Owed":       rec.get("amount", ""),
            "Seller Score":           rec.get("score", 0),
            "Motivated Seller Flags": "; ".join(rec.get("flags", [])),
            "Source":                 f"Richland County ROD",
            "Public Records URL":     rec.get("clerk_url", ""),
        })

    with open(CSV_PATH, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    log(f"  ✓ GHL CSV written → {CSV_PATH} ({len(rows)} rows)")

# ══════════════════════════════════════════════════════════════════════════════
# ENTRYPOINT
# ══════════════════════════════════════════════════════════════════════════════

async def main():
    date_to   = today_str()
    date_from = week_ago()

    log("=" * 60)
    log(f"Richland County SC Lead Scraper")
    log(f"Date range: {date_from} → {date_to}")
    log(f"Doc types:  {', '.join(DOC_TYPE_MAP.keys())}")
    log("=" * 60)

    # 1. Parcel data (load before scraping so it's ready for enrichment)
    parcels = ParcelLookup()
    parcels.load()

    # 2. Scrape ROD portal
    log("\n── Scraping Register of Deeds ──────────────────────────────")
    records = await scrape_all_doc_types(date_from, date_to)
    log(f"\nTotal raw records scraped: {len(records)}")

    # 3. Enrich with parcel data + score
    log("\n── Enriching with parcel data ──────────────────────────────")
    records = enrich_records(records, parcels)

    # 4. Sort by score desc
    records.sort(key=lambda r: r.get("score", 0), reverse=True)

    # 5. Write outputs
    log("\n── Writing outputs ─────────────────────────────────────────")
    write_json(records, date_from, date_to)
    write_ghl_csv(records)

    log("\n✅ Done.")
    log(f"   Total leads: {len(records)}")
    log(f"   Scores ≥ 60: {sum(1 for r in records if r.get('score', 0) >= 60)}")
    log(f"   With address: {sum(1 for r in records if r.get('prop_address'))}")


if __name__ == "__main__":
    asyncio.run(main())
