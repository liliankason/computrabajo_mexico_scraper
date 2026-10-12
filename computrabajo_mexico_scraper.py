#!/usr/bin/env python3
"""
Computrabajo Mexico (mx.computrabajo.com) job scraper.

  1. Discover location URLs (/empleos-en-<place>) from the homepage
     (with diagnostics + sitemap fallback).
  2. Paginate each location (?p=2, ?p=3 ...) until a page has zero jobs.
  3. Read each job's JSON-LD JobPosting (HTML fallback).
  4. ALWAYS write every job to mexico_scraped_jobs.csv (full column set),
     and additionally post to WordPress when credentials are set.
  5. Resumable: progress (location URL, page, position) saved after every job.
  6. On GitHub Actions (GIT_AUTO_PUSH=1) the CSV + trackers are committed and
     pushed to the repo IMMEDIATELY after each job, so the CSV in the repo is
     always up to date instead of only appearing when the run ends.

Run: python computrabajo_mexico_scraper.py
"""
import os
import re
import csv
import sys
import json
import time
import html
import base64
import hashlib
import logging
import subprocess
from datetime import datetime
from urllib.parse import urljoin, urlparse

import requests
from bs4 import BeautifulSoup

# ════════════════════════════════════════════════════════════════════════════
# CONFIG
# ════════════════════════════════════════════════════════════════════════════
BASE_URL = "https://mx.computrabajo.com"   # real website domain — do not change
HOME_URL = BASE_URL + "/"

REQUEST_TIMEOUT = 20
VERBOSE = True
PROCESSED_IDS_FILE = "mexico_processed.csv"
PROGRESS_FILE = "mexico_computrabajo_progress.json"
SCRAPED_JOBS_CSV = "mexico_scraped_jobs.csv"
DONE_FLAG_FILE = "mexico_SCRAPE_COMPLETE.flag"
DIAG_FILE = "mexico_fetch_diagnostics.json"
DEBUG_LOG_FILE = "mexico_debug.log"
HOMEPAGE_DEBUG_FILE = "mexico_homepage_debug.html"

MAX_RUNTIME_SECONDS = int(os.environ.get("MAX_RUNTIME_SECONDS", "300"))
SCRIPT_START_TIME = time.time()

# ── Git auto-push (set GIT_AUTO_PUSH=1 in the workflow) ──────────────────────
# Commits + pushes the CSV and trackers to the repo every N saved jobs.
# N=1 means "immediately after every job". The (large) debug log is NOT pushed
# per job; the workflow's final step still commits it at the end of the run.
GIT_AUTO_PUSH = os.environ.get("GIT_AUTO_PUSH", "").strip() == "1"
GIT_PUSH_EVERY_N_JOBS = max(1, int(os.environ.get("GIT_PUSH_EVERY_N_JOBS", "1") or "1"))
GIT_PUSH_FILES = [SCRAPED_JOBS_CSV, PROCESSED_IDS_FILE, PROGRESS_FILE]
_jobs_since_push = 0


def time_budget_exceeded() -> bool:
    return (time.time() - SCRIPT_START_TIME) >= MAX_RUNTIME_SECONDS


# NOTE: "br" (brotli) is deliberately NOT in Accept-Encoding. `requests` cannot
# decode brotli unless the `brotli` package is installed, which yields a garbled
# body and makes every selector/link search find nothing.
HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8",
    "Accept-Language": "es-MX,es;q=0.9,en;q=0.8",
    "Accept-Encoding": "gzip, deflate",
    "Sec-Fetch-Dest": "document",
    "Sec-Fetch-Mode": "navigate",
    "Sec-Fetch-Site": "none",
    "Sec-Fetch-User": "?1",
    "Upgrade-Insecure-Requests": "1",
    "Connection": "keep-alive",
}

# ── WordPress ─────────────────────────────────────────────────────────────────
# LOCAL RUNS: put credentials here. Blank them before pushing to a public repo.
_LOCAL_WP_BASE_URL     = ""   # e.g. "https://yoursite.com/wp-json/wp/v2"
_LOCAL_WP_USERNAME     = ""
_LOCAL_WP_APP_PASSWORD = ""

WP_URL      = _LOCAL_WP_BASE_URL or os.environ.get("WP_BASE_URL", "")
WP_USER     = _LOCAL_WP_USERNAME or os.environ.get("WP_USERNAME", "")
WP_PASSWORD = _LOCAL_WP_APP_PASSWORD or os.environ.get("WP_APP_PASSWORD", "")

WP_BASE        = WP_URL.rstrip("/")
WP_JOBS_URL    = f"{WP_BASE}/job-listings"
WP_COMPANY_URL = f"{WP_BASE}/companies"
WP_MEDIA_URL   = f"{WP_BASE}/media"

_LOCAL_INTERNAL_BOT_KEY = ""
INTERNAL_BOT_KEY = _LOCAL_INTERNAL_BOT_KEY or os.environ.get("INTERNAL_BOT_KEY", "").strip()

JOB_TYPE_MAPPING = {
    "full_time": "full-time", "full-time": "full-time", "fulltime": "full-time",
    "part_time": "part-time", "part-time": "part-time", "parttime": "part-time",
    "contractor": "contract", "contract": "contract",
    "temporary": "temporary", "temp": "temporary",
    "intern": "internship", "internship": "internship",
    "volunteer": "volunteer",
    "per_diem": "contract", "other": "full-time",
}

# ── Logging ───────────────────────────────────────────────────────────────────
logger = logging.getLogger()
logger.setLevel(logging.DEBUG)
logger.handlers.clear()

_fh = logging.FileHandler(DEBUG_LOG_FILE, encoding="utf-8")
_fh.setLevel(logging.DEBUG)
_fh.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
logger.addHandler(_fh)

try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass

_ch = logging.StreamHandler(sys.stdout)
_ch.setLevel(logging.DEBUG if VERBOSE else logging.INFO)
_ch.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
logger.addHandler(_ch)

if INTERNAL_BOT_KEY:
    logger.info(f"[STARTUP CHECK] INTERNAL_BOT_KEY is SET (length={len(INTERNAL_BOT_KEY)}).")
else:
    logger.warning("[STARTUP CHECK] INTERNAL_BOT_KEY is EMPTY/MISSING — X-Internal-Auth will NOT be sent.")

if GIT_AUTO_PUSH:
    logger.info(f"[STARTUP CHECK] GIT_AUTO_PUSH is ON — committing/pushing every "
                f"{GIT_PUSH_EVERY_N_JOBS} saved job(s).")
else:
    logger.info("[STARTUP CHECK] GIT_AUTO_PUSH is OFF — files are only written locally.")


def require_wp_config() -> bool:
    missing = [n for n, v in
               [("WP_BASE_URL", WP_URL), ("WP_USERNAME", WP_USER), ("WP_APP_PASSWORD", WP_PASSWORD)]
               if not v]
    if missing:
        logger.warning(f"⚠️  WordPress credentials not set ({', '.join(missing)}) — "
                       f"WP posting DISABLED. Jobs are still saved to {SCRAPED_JOBS_CSV}.")
        return False
    return True


# ════════════════════════════════════════════════════════════════════════════
# GIT AUTO-PUSH
# ════════════════════════════════════════════════════════════════════════════
def _git(*args, timeout: int = 120) -> subprocess.CompletedProcess:
    cmd = ["git", *args]
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    logger.debug(f"    $ {' '.join(cmd)} → rc={result.returncode}"
                 + (f" | {result.stdout.strip()[:300]}" if result.stdout.strip() else "")
                 + (f" | {result.stderr.strip()[:300]}" if result.stderr.strip() else ""))
    return result


def git_push_progress(force: bool = False):
    """Commit + push the CSV and trackers. Never raises — a failed push must not
    stop the scrape (the workflow's final commit step is the safety net)."""
    global _jobs_since_push
    if not GIT_AUTO_PUSH:
        return
    _jobs_since_push += 1
    if not force and _jobs_since_push < GIT_PUSH_EVERY_N_JOBS:
        return

    try:
        files = [f for f in GIT_PUSH_FILES if os.path.exists(f)]
        if not files:
            return

        _git("config", "user.name", "computrabajo-scraper-bot")
        _git("config", "user.email", "actions@users.noreply.github.com")

        _git("add", "-f", "--", *files)
        if _git("diff", "--cached", "--quiet").returncode == 0:
            logger.debug("    git: nothing new to commit.")
            _jobs_since_push = 0
            return

        commit = _git("commit", "-m", "Scraper progress update [skip ci]")
        if commit.returncode != 0:
            logger.warning(f"    git commit failed: {commit.stderr.strip()[:300]}")
            return

        pushed = False
        for attempt in range(1, 4):
            if _git("push").returncode == 0:
                pushed = True
                break
            logger.warning(f"    git push attempt {attempt}/3 failed — pulling (rebase) and retrying.")
            rebase = _git("pull", "--rebase", "--autostash")
            if rebase.returncode != 0:
                _git("rebase", "--abort")
            time.sleep(2 * attempt)

        if pushed:
            logger.info("📤 CSV + trackers pushed to repo.")
            _jobs_since_push = 0
        else:
            logger.warning("📤 git push failed after 3 attempts — will retry on the next job "
                           "and again in the workflow's final commit step.")
    except Exception as e:
        logger.warning(f"    git auto-push error (ignored): {e}")


# ════════════════════════════════════════════════════════════════════════════
# HTTP
# ════════════════════════════════════════════════════════════════════════════
SESSION = requests.Session()
SESSION.headers.update(HEADERS)


def wp_headers() -> dict:
    token = base64.b64encode(f"{WP_USER}:{WP_PASSWORD}".encode()).decode()
    headers = {"Authorization": f"Basic {token}", "Content-Type": "application/json"}
    if INTERNAL_BOT_KEY:
        headers["X-Internal-Auth"] = INTERNAL_BOT_KEY
    return headers


# Strict signatures only. Words like "cloudflare" or "captcha" alone appear in
# normal pages' scripts and caused false positives.
_BLOCK_SIGNATURES = [
    "checking your browser", "cf-browser-verification", "attention required! | cloudflare",
    "just a moment...", "px-captcha", "perimeterx", "distil_r_captcha",
    "request unsuccessful. incapsula", "are you a robot", "unusual traffic from your computer",
    "verify you are human", "access denied",
]


def looks_blocked(html_text: str, status_code: int = 200) -> str:
    if status_code in (403, 429, 503):
        return f"http_{status_code}"
    lowered = html_text.lower()
    # Block pages are small; real pages are large. Only scan small bodies.
    if len(lowered) < 30000:
        for sig in _BLOCK_SIGNATURES:
            if sig in lowered:
                return sig
    return ""


def get_soup(url: str, timeout: int = REQUEST_TIMEOUT, retries: int = 3) -> BeautifulSoup:
    """GET with retries/backoff. Raises on persistent failure."""
    last_err = None
    for attempt in range(1, retries + 1):
        try:
            resp = SESSION.get(url, timeout=timeout)
            resp.encoding = "utf-8"
            logger.debug(f"    GET {url} → HTTP {resp.status_code} ({len(resp.text):,} chars)")
            block = looks_blocked(resp.text, resp.status_code)
            if block:
                raise RuntimeError(f"blocked/rate-limited ({block})")
            if resp.status_code >= 400:
                raise RuntimeError(f"HTTP {resp.status_code}")
            return BeautifulSoup(resp.text, "html.parser")
        except Exception as e:
            last_err = e
            logger.warning(f"    attempt {attempt}/{retries} failed for {url}: {e}")
            if attempt < retries:
                time.sleep(3 * attempt)
    raise RuntimeError(f"giving up on {url}: {last_err}")


def fetch_homepage_with_diagnostics() -> tuple:
    last_exception = None
    diagnostics = {"url": HOME_URL, "attempts": []}

    for attempt in range(1, 4):
        info = {"attempt": attempt}
        try:
            resp = SESSION.get(HOME_URL, timeout=REQUEST_TIMEOUT)
            resp.encoding = "utf-8"
            body = resp.text
            block_sig = looks_blocked(body, resp.status_code)
            info.update({
                "status_code": resp.status_code,
                "response_headers": dict(resp.headers),
                "body_length": len(body),
                "body_snippet": body[:1000],
                "block_signature_matched": block_sig or None,
                "final_url_after_redirects": resp.url,
            })
            diagnostics["attempts"].append(info)

            if resp.status_code == 200 and not block_sig and len(body) > 2000:
                logger.info(f"✅ Homepage fetched cleanly (HTTP 200, {len(body):,} chars).")
                diagnostics["outcome"] = "ok"
                return BeautifulSoup(body, "html.parser"), diagnostics

            if block_sig:
                logger.error(f"🚫 Homepage looks blocked (signature: '{block_sig}'). See {DIAG_FILE}.")
            else:
                logger.warning(f"⚠️  Homepage response unusual (HTTP {resp.status_code}, "
                               f"{len(body):,} chars) — retrying.")
        except Exception as e:
            last_exception = e
            info["exception"] = str(e)
            diagnostics["attempts"].append(info)
            logger.warning(f"⚠️  Homepage fetch attempt {attempt} raised: {e}")

        if attempt < 3:
            time.sleep(3 * attempt)

    diagnostics["outcome"] = "blocked_or_failed"
    if last_exception:
        diagnostics["final_exception"] = str(last_exception)
    return None, diagnostics


def save_diagnostics(diagnostics: dict):
    try:
        with open(DIAG_FILE, "w", encoding="utf-8") as f:
            json.dump(diagnostics, f, indent=2, ensure_ascii=False)
        logger.info(f"📝 Wrote {DIAG_FILE}")
    except OSError as e:
        logger.error(f"Failed to write {DIAG_FILE}: {e}")


# ════════════════════════════════════════════════════════════════════════════
# SANITIZATION / HELPERS
# ════════════════════════════════════════════════════════════════════════════
def sanitize(value) -> str:
    if value is None:
        return ""
    if not isinstance(value, str):
        value = str(value)
    value = html.unescape(value)
    # keep paragraph/list structure before stripping tags
    value = re.sub(r"(?i)<br\s*/?>|</p>|</li>|</div>|</h[1-6]>", "\n", value)
    value = re.sub(r"(?i)<li[^>]*>", "• ", value)
    text = re.sub(r"<[^>]+>", " ", value)
    text = re.sub(r"[\x00-\x08\x0B\x0C\x0E-\x1F\x7F]", "", text)
    text = re.sub(r"[ \t]+", " ", text)
    text = re.sub(r" ?\n ?", "\n", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()


def first_str(value) -> str:
    """JSON-LD fields can be str, list, dict or None — flatten to one string."""
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    if isinstance(value, list):
        return ", ".join(x for x in (first_str(v) for v in value) if x)
    if isinstance(value, dict):
        return first_str(value.get("name") or value.get("value") or value.get("description") or "")
    return str(value)


def normalise_job_type(raw: str) -> str:
    return JOB_TYPE_MAPPING.get((raw or "").lower().strip().split(",")[0].strip(), "full-time")


def add_three_months(posted_date: datetime) -> str:
    month = posted_date.month - 1 + 3
    year = posted_date.year + month // 12
    month = month % 12 + 1
    day = min(posted_date.day, 28)
    return datetime(year, month, day).strftime("%Y-%m-%d")


def make_job_id(job_url: str) -> str:
    return hashlib.md5(job_url.encode()).hexdigest()[:16]


def slugify(text: str, maxlen: int = 80) -> str:
    return re.sub(r"-{2,}", "-", re.sub(r"[^a-z0-9-]", "-", text.lower().strip())).strip("-")[:maxlen]


# ════════════════════════════════════════════════════════════════════════════
# SCRAPED-JOBS CSV (full record of everything scraped)
# ════════════════════════════════════════════════════════════════════════════
CSV_COLUMNS = [
    "Page", "Position On Page", "Job Title", "Job Description", "Job Type",
    "Job Type (Normalised)", "Location", "Job Field", "Qualification", "Experience",
    "Salary", "Date Posted", "Deadline", "Estimated Deadline", "Application",
    "Company Name", "Company URL", "Company Logo", "Company Industry", "Company Founded",
    "Company Type", "Company Website", "Company Address", "Company Details",
    "Job URL", "Job ID",
]


def _init_scraped_jobs_csv():
    """Creates the CSV with the correct header. If an old CSV exists with a
    different header, it's backed up (never deleted) and a fresh one is started."""
    if os.path.exists(SCRAPED_JOBS_CSV):
        try:
            with open(SCRAPED_JOBS_CSV, newline="", encoding="utf-8") as f:
                header = next(csv.reader(f), [])
        except OSError:
            header = []
        if header == CSV_COLUMNS:
            return
        backup = f"{SCRAPED_JOBS_CSV}.old-{datetime.now().strftime('%Y%m%d%H%M%S')}"
        os.rename(SCRAPED_JOBS_CSV, backup)
        logger.warning(f"Old CSV header differed — backed up to {backup}")
    with open(SCRAPED_JOBS_CSV, "w", newline="", encoding="utf-8") as f:
        csv.DictWriter(f, fieldnames=CSV_COLUMNS).writeheader()


def load_csv_job_ids() -> set:
    _init_scraped_jobs_csv()
    ids = set()
    with open(SCRAPED_JOBS_CSV, newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            if row.get("Job ID"):
                ids.add(row["Job ID"])
    return ids


def save_job_to_csv(job: dict, page_num: int, position: int, job_id: str):
    _init_scraped_jobs_csv()
    row = {
        "Page": page_num,
        "Position On Page": position,
        "Job Title": job["job_title"],
        "Job Description": job["job_description"],
        "Job Type": job["job_type_raw"],
        "Job Type (Normalised)": job["job_type"],
        "Location": job["job_location"],
        "Job Field": job["job_field"],
        "Qualification": job["job_qualifications"],
        "Experience": job["job_experience"],
        "Salary": job["salary_range"],
        "Date Posted": job["date_posted"],
        "Deadline": job["deadline"],
        "Estimated Deadline": job["estimated_deadline"],
        "Application": job["application"],
        "Company Name": job["company_name"],
        "Company URL": job["company_url"],
        "Company Logo": job["company_logo"],
        "Company Industry": job["company_industry"],
        "Company Founded": job["company_founded"],
        "Company Type": job["company_type"],
        "Company Website": job["company_website"],
        "Company Address": job["company_address"],
        "Company Details": job["company_details"],
        "Job URL": job["job_url"],
        "Job ID": job_id,
    }
    with open(SCRAPED_JOBS_CSV, "a", newline="", encoding="utf-8") as f:
        csv.DictWriter(f, fieldnames=CSV_COLUMNS).writerow(row)
        f.flush()
        os.fsync(f.fileno())
    logger.info(f"💾 Saved to {SCRAPED_JOBS_CSV}: '{job['job_title']}' (job id {job_id})")


# ════════════════════════════════════════════════════════════════════════════
# DEDUP TRACKER
# ════════════════════════════════════════════════════════════════════════════
def _init_tracker():
    if not os.path.exists(PROCESSED_IDS_FILE):
        with open(PROCESSED_IDS_FILE, "w", newline="", encoding="utf-8") as f:
            csv.writer(f).writerow(
                ["Job ID", "Job URL", "Job Title", "Status", "Timestamp", "Location", "Page"]
            )


def load_processed_ids() -> set:
    _init_tracker()
    with open(PROCESSED_IDS_FILE, newline="", encoding="utf-8") as f:
        return {row["Job ID"] for row in csv.DictReader(f)}


def mark_processed(job_id, job_url, title, status, location=None, page_num=None):
    _init_tracker()
    with open(PROCESSED_IDS_FILE, "a", newline="", encoding="utf-8") as f:
        csv.writer(f).writerow([
            job_id, job_url, title, status, datetime.now().isoformat(),
            location or "", page_num if page_num is not None else "",
        ])
        f.flush()
        os.fsync(f.fileno())


# ════════════════════════════════════════════════════════════════════════════
# PROGRESS TRACKER
# ════════════════════════════════════════════════════════════════════════════
def load_progress() -> dict:
    if os.path.exists(PROGRESS_FILE):
        try:
            with open(PROGRESS_FILE, encoding="utf-8") as f:
                return json.load(f)
        except (ValueError, OSError):
            pass
    return {"location_index": 0, "location_url": "", "page": 1, "position": 0}


def save_progress(location_index: int, page: int, position: int = 0,
                  location_url: str = "", note: str = None):
    payload = {
        "location_index": location_index,
        "location_url": location_url,
        "page": page,
        "position": position,   # last COMPLETED position on that page
    }
    if note:
        payload["note"] = note
    payload["last_updated"] = datetime.now().isoformat()
    tmp = PROGRESS_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(payload, f)
    os.replace(tmp, PROGRESS_FILE)   # atomic: never leaves a half-written file


# ════════════════════════════════════════════════════════════════════════════
# STEP 1 — LOCATIONS
# ════════════════════════════════════════════════════════════════════════════
_LOCATION_HREF_RE = re.compile(r"^/empleos-en-[a-z0-9-]+/?$", re.IGNORECASE)
_CANDIDATE_SITEMAP_PATHS = [
    "/sitemap.xml", "/sitemap_index.xml", "/sitemaps/sitemap.xml", "/sitemap-ciudades.xml",
]


def _try_sitemaps() -> list:
    urls, seen = [], set()
    for path in _CANDIDATE_SITEMAP_PATHS:
        sitemap_url = BASE_URL + path
        try:
            resp = SESSION.get(sitemap_url, timeout=10)
            if resp.status_code != 200 or "<" not in resp.text[:50]:
                continue
            soup = BeautifulSoup(resp.text, "xml")   # requires lxml
            for loc in soup.find_all("loc"):
                href = loc.get_text(strip=True)
                if _LOCATION_HREF_RE.match(urlparse(href).path) and href not in seen:
                    seen.add(href)
                    urls.append(href)
            if urls:
                logger.info(f"📍 Found {len(urls)} location URLs via sitemap: {sitemap_url}")
                return urls
        except Exception:
            continue
    return urls


def get_location_urls() -> list:
    logger.info(f"Fetching homepage: {HOME_URL}")
    soup, diagnostics = fetch_homepage_with_diagnostics()
    save_diagnostics(diagnostics)

    if soup is None:
        logger.error(f"❌ No clean homepage response — see {DIAG_FILE}.")
        return []

    seen, urls = set(), []

    def _collect(anchors):
        for a in anchors:
            href = a.get("href", "").strip()
            if not href or (href.startswith("http") and BASE_URL not in href):
                continue
            full = urljoin(BASE_URL, href)
            if full not in seen:
                seen.add(full)
                urls.append(full)

    container = soup.select_one("div.lL")
    if container:
        _collect(container.select("ul#content_1 a[href]"))
        if urls:
            logger.info(f"📍 Found {len(urls)} location URLs via div.lL.")

    if not urls:
        logger.info("div.lL empty — scanning page for /empleos-en-<place> links.")
        _collect(a for a in soup.select("a[href]")
                 if _LOCATION_HREF_RE.match(urlparse(a.get("href", "")).path or a.get("href", "")))

    if not urls:
        logger.info("No homepage links — trying sitemaps.")
        for u in _try_sitemaps():
            if u not in seen:
                seen.add(u)
                urls.append(u)

    if not urls:
        try:
            with open(HOMEPAGE_DEBUG_FILE, "w", encoding="utf-8") as f:
                f.write(str(soup))
            logger.error(f"❌ No location URLs found. Homepage HTML dumped to {HOMEPAGE_DEBUG_FILE}.")
        except OSError as e:
            logger.error(f"❌ No location URLs found, and debug dump failed: {e}")
    else:
        logger.info(f"📍 Found {len(urls)} location URLs.")
        for i, u in enumerate(urls):
            logger.debug(f"    [{i}] {u}")
    return urls


# ════════════════════════════════════════════════════════════════════════════
# STEP 2 — LISTING PAGES
# ════════════════════════════════════════════════════════════════════════════
def build_page_url(location_url: str, page_num: int) -> str:
    if page_num <= 1:
        return location_url
    sep = "&" if "?" in location_url else "?"
    return f"{location_url}{sep}p={page_num}"


def scrape_job_list_page(location_url: str, page_num: int):
    """Returns list of job URLs, or None if the fetch FAILED (distinct from an
    empty-but-successful page, which returns [])."""
    url = build_page_url(location_url, page_num)
    logger.info(f"Fetching listing page {page_num}: {url}")
    try:
        soup = get_soup(url)
    except Exception as e:
        logger.error(f"Error fetching {url}: {e}")
        return None

    urls, seen = [], set()
    for article in soup.select("article.box_offer"):
        a = article.select_one("h2 a.js-o-link[href]")
        if not a:
            continue
        full = urljoin(BASE_URL, a["href"].split("#")[0])
        if full not in seen:
            seen.add(full)
            urls.append(full)

    logger.info(f"Found {len(urls)} job URLs on page {page_num}")
    return urls


# ════════════════════════════════════════════════════════════════════════════
# STEP 3 — JOB DETAILS
# ════════════════════════════════════════════════════════════════════════════
def _find_jobposting_jsonld(soup: BeautifulSoup) -> dict:
    for script in soup.select('script[type="application/ld+json"]'):
        raw = script.string or script.get_text()
        if not raw or "JobPosting" not in raw:
            continue
        try:
            data = json.loads(raw)
        except (ValueError, TypeError):
            continue
        candidates = data.get("@graph", [data]) if isinstance(data, dict) else data
        if not isinstance(candidates, list):
            candidates = [candidates]
        for entry in candidates:
            if isinstance(entry, dict):
                t = entry.get("@type")
                if t == "JobPosting" or (isinstance(t, list) and "JobPosting" in t):
                    return entry
    return {}


def _html_fallback_fields(soup: BeautifulSoup) -> dict:
    title_el = soup.select_one("h1.fwB.fs24") or soup.select_one("h1")
    title = title_el.get_text(strip=True) if title_el else ""

    desc_el = soup.select_one('div[div-link="oferta"] p.mbB')
    description = desc_el.get_text("\n", strip=True) if desc_el else ""

    company_loc_el = soup.select_one("main p.fs16")
    company, location = "", ""
    if company_loc_el:
        parts = company_loc_el.get_text(strip=True).split(" - ")
        if len(parts) >= 2:
            company, location = parts[0], parts[-1]
        elif parts:
            company = parts[0]

    salary_el = soup.select_one('div[div-link="oferta"] span.tag.base')
    salary = salary_el.get_text(strip=True) if salary_el else ""

    return {
        "title": title,
        "description": description,
        "hiringOrganization": {"name": company},
        "jobLocation": {"address": {"addressLocality": location}},
        "baseSalary": {"value": {"value": salary}} if salary else {},
    }


def scrape_job_details(job_url: str) -> dict:
    soup = get_soup(job_url)
    jp = _find_jobposting_jsonld(soup)
    if not jp:
        logger.warning(f"No JobPosting JSON-LD, using HTML fallback: {job_url}")
        jp = _html_fallback_fields(soup)
        if not jp.get("title"):
            logger.warning(f"Fallback extraction failed — skipping: {job_url}")
            return {}

    title = first_str(jp.get("title"))
    description = first_str(jp.get("description"))
    if not title or not description:
        logger.warning(f"Missing title/description — skipping: {job_url}")
        return {}

    org = jp.get("hiringOrganization") or {}
    if not isinstance(org, dict):
        org = {"name": first_str(org)}
    company_name = first_str(org.get("name"))
    company_logo = first_str(org.get("logo"))
    company_url = first_str(org.get("url") or org.get("sameAs"))
    company_website = first_str(org.get("sameAs") or org.get("url"))
    company_details = first_str(org.get("description"))
    company_founded = first_str(org.get("foundingDate"))
    company_type = first_str(org.get("@type")) if org.get("@type") != "Organization" else ""

    loc_raw = jp.get("jobLocation") or {}
    if isinstance(loc_raw, list):
        loc_raw = loc_raw[0] if loc_raw else {}
    addr = (loc_raw.get("address") if isinstance(loc_raw, dict) else {}) or {}
    if isinstance(addr, str):
        addr = {"addressLocality": addr}
    location_parts = [p for p in (addr.get("addressRegion"), addr.get("addressLocality")) if p]
    job_location = ", ".join(dict.fromkeys(location_parts))
    street = first_str(addr.get("streetAddress"))
    company_address = ", ".join(x for x in (street, job_location) if x)

    base_salary = jp.get("baseSalary") or {}
    salary_val = (base_salary.get("value") or {}) if isinstance(base_salary, dict) else {}
    if isinstance(salary_val, dict):
        mn, mx, single = salary_val.get("minValue"), salary_val.get("maxValue"), salary_val.get("value", "")
        amount = f"{mn}-{mx}" if mn and mx else (single or mn or mx or "")
    else:
        amount = salary_val
    currency = jp.get("salaryCurrency") or (base_salary.get("currency") if isinstance(base_salary, dict) else "") or "USD"
    salary_range = f"{amount} {currency}".strip() if amount else ""

    date_posted_str = first_str(jp.get("datePosted"))
    date_posted = None
    for fmt in ("%Y-%m-%dT%H:%M:%S", "%Y-%m-%d"):
        try:
            candidate = date_posted_str[:19] if "T" in fmt else date_posted_str[:10]
            date_posted = datetime.strptime(candidate, fmt)
            break
        except (ValueError, TypeError):
            continue

    estimated_deadline = add_three_months(date_posted) if date_posted else ""
    deadline = first_str(jp.get("validThrough")) or estimated_deadline

    job_type_raw = first_str(jp.get("employmentType"))
    job_type = normalise_job_type(job_type_raw)

    ident = jp.get("identifier")
    identifier = first_str(ident.get("value")) if isinstance(ident, dict) else first_str(ident)

    industry = first_str(jp.get("industry"))
    qualification = first_str(jp.get("educationRequirements") or jp.get("qualifications"))
    experience = first_str(jp.get("experienceRequirements"))
    if isinstance(jp.get("experienceRequirements"), dict):
        m = jp["experienceRequirements"].get("monthsOfExperience")
        if m:
            experience = f"{m} months"

    job = {
        "job_title": sanitize(title),
        "job_type_raw": sanitize(job_type_raw),
        "job_type": sanitize(job_type),
        "job_qualifications": sanitize(qualification),
        "job_experience": sanitize(experience),
        "job_location": sanitize(job_location) or "Mexico",
        "job_field": sanitize(industry),
        "date_posted": sanitize(date_posted_str),
        "deadline": sanitize(deadline),
        "job_description": sanitize(description),
        "application": sanitize(job_url),
        "company_url": sanitize(company_url),
        "company_name": sanitize(company_name),
        "company_logo": sanitize(company_logo),
        "company_industry": sanitize(industry),
        "company_founded": sanitize(company_founded),
        "company_type": sanitize(company_type),
        "company_website": sanitize(company_website),
        "company_address": sanitize(company_address),
        "company_details": sanitize(company_details),
        "job_url": sanitize(job_url),
        "estimated_deadline": sanitize(estimated_deadline),
        "salary_range": sanitize(salary_range),
        "external_id": sanitize(identifier),
    }
    log_scraped_job(job_url, job)
    return job


def log_scraped_job(job_url: str, job: dict):
    d = job["job_description"]
    preview = (d[:200] + "…") if len(d) > 200 else d
    logger.info(
        "    ┌─ SCRAPED JOB ─────────────────────────────────────────\n"
        f"    │ URL          : {job_url}\n"
        f"    │ Title        : {job['job_title']}\n"
        f"    │ Company      : {job['company_name'] or '(none)'}\n"
        f"    │ Location     : {job['job_location']}\n"
        f"    │ Job type     : {job['job_type_raw'] or '(none)'} → {job['job_type']}\n"
        f"    │ Salary       : {job['salary_range'] or '(not listed)'}\n"
        f"    │ Industry     : {job['job_field'] or '(none)'}\n"
        f"    │ Date posted  : {job['date_posted'] or '(unknown)'}\n"
        f"    │ Deadline     : {job['deadline'] or '(none)'}\n"
        f"    │ External ID  : {job['external_id'] or '(none)'}\n"
        f"    │ Description  : {preview}\n"
        "    └───────────────────────────────────────────────────────"
    )


# ════════════════════════════════════════════════════════════════════════════
# WORDPRESS
# ════════════════════════════════════════════════════════════════════════════
def upload_logo(logo_url: str):
    if not logo_url or not logo_url.startswith("http"):
        return None
    ext = logo_url.lower().rsplit(".", 1)[-1].split("?")[0]
    if ext not in ("png", "jpg", "jpeg", "webp"):
        return None
    try:
        img = SESSION.get(logo_url, timeout=15)
        img.raise_for_status()
        headers = wp_headers()
        headers["Content-Disposition"] = f"attachment; filename={logo_url.split('/')[-1].split('?')[0]}"
        headers["Content-Type"] = img.headers.get("content-type", "image/jpeg")
        r = SESSION.post(WP_MEDIA_URL, headers=headers, data=img.content,
                         auth=(WP_USER, WP_PASSWORD), timeout=20)
        r.raise_for_status()
        return r.json().get("id")
    except Exception as e:
        logger.error(f"Logo upload error: {e}")
        return None


_term_cache = {}


def get_or_create_term(taxonomy_url: str, name: str):
    if not name or not name.strip():
        return None
    slug = slugify(name)
    cache_key = (taxonomy_url, slug)
    if cache_key in _term_cache:
        return _term_cache[cache_key]
    try:
        r = SESSION.get(f"{taxonomy_url}?slug={slug}", headers=wp_headers(), timeout=10)
        terms = r.json()
        if isinstance(terms, list) and terms:
            _term_cache[cache_key] = terms[0]["id"]
            return terms[0]["id"]
    except Exception:
        pass
    try:
        r = SESSION.post(taxonomy_url, json={"name": name, "slug": slug},
                         headers=wp_headers(), auth=(WP_USER, WP_PASSWORD), timeout=10)
        term_id = r.json().get("id")
        _term_cache[cache_key] = term_id
        return term_id
    except Exception as e:
        logger.error(f"Term create error '{name}': {e}")
        return None


def ensure_job_type_terms():
    for label in ["Full Time", "Part Time", "Contract", "Temporary", "Internship", "Volunteer"]:
        get_or_create_term(f"{WP_BASE}/job_listing_type", label)


def save_company(job: dict):
    name = job["company_name"]
    if not name:
        return None
    slug = slugify(name)
    try:
        r = SESSION.get(f"{WP_COMPANY_URL}?slug={slug}", headers=wp_headers(), timeout=10)
        posts = r.json()
        if isinstance(posts, list) and posts:
            logger.info(f"⏭ Company exists: {name}")
            return posts[0]["id"]
    except Exception:
        pass

    attachment_id = upload_logo(job["company_logo"])
    payload = {
        "title": name,
        "slug": slug,
        "content": job["company_details"],
        "status": "publish",
        "featured_media": attachment_id or 0,
        "meta": {
            "_company_name": name,
            "_company_logo": str(attachment_id) if attachment_id else "",
            "_company_industry": job["company_industry"],
            "_company_website": job["company_website"],
        },
    }
    try:
        r = SESSION.post(WP_COMPANY_URL, json=payload, headers=wp_headers(),
                         auth=(WP_USER, WP_PASSWORD), timeout=20)
        r.raise_for_status()
        post = r.json()
        logger.info(f"✅ Company posted: {name} → ID {post.get('id')}")
        return post.get("id")
    except Exception as e:
        logger.error(f"Company post error '{name}': {e}")
        return None


def save_job(job: dict, job_id: str):
    title       = job["job_title"]
    description = job["job_description"]
    location    = job["job_location"] or "Mexico"
    job_type_s  = job["job_type"] or "full-time"
    company     = job["company_name"]
    deadline    = job["deadline"] or job["estimated_deadline"]

    # Slug includes the job id so different jobs with the same title
    # are no longer wrongly treated as duplicates.
    slug = f"{slugify(title, 60)}-{job_id[:8]}"
    try:
        r = SESSION.get(f"{WP_JOBS_URL}?slug={slug}", headers=wp_headers(), timeout=10)
        posts = r.json()
        if isinstance(posts, list) and posts:
            logger.info(f"⏭ Job already on WP: {title}")
            return posts[0]["id"], posts[0].get("link")
    except Exception:
        pass

    attachment_id    = upload_logo(job["company_logo"])
    region_term_id   = get_or_create_term(f"{WP_BASE}/job_listing_region", location)
    job_type_term_id = get_or_create_term(f"{WP_BASE}/job_listing_type", job_type_s.replace("-", " ").title())

    payload = {
        "title": title,
        "slug": slug,
        "content": description,
        "status": "publish",
        "featured_media": attachment_id or 0,
        "meta": {
            "_job_title":          title,
            "_job_location":       location,
            "_job_type":           job_type_s,
            "_job_description":    description,
            "_application":        job["application"],
            "_job_expires":        deadline,
            "_company_name":       company,
            "_company_website":    job["company_website"],
            "_company_logo":       str(attachment_id) if attachment_id else "",
            "_company_industry":   job["company_industry"],
            "_company_address":    job["company_address"],
            "_job_qualifications": job["job_qualifications"],
            "_job_experiences":    job["job_experience"],
            "_job_field":          job["job_field"],
            "_job_source_url":     job["job_url"],
            "_job_salary":         job["salary_range"],
            "_external_id":        job["external_id"],
        },
    }
    if region_term_id:
        payload["job_listing_region"] = [region_term_id]
    if job_type_term_id:
        payload["job_listing_type"] = [job_type_term_id]

    for attempt in range(3):
        try:
            r = SESSION.post(WP_JOBS_URL, json=payload, headers=wp_headers(),
                             auth=(WP_USER, WP_PASSWORD), timeout=25)
            r.raise_for_status()
            post = r.json()
            logger.info(f"✅ Job posted: '{title}' → WP ID {post.get('id')}")
            return post.get("id"), post.get("link")
        except Exception as e:
            logger.error(f"Job post attempt {attempt + 1} failed: {e}")
            if attempt < 2:
                time.sleep(2 ** attempt)
    return None, None


# ════════════════════════════════════════════════════════════════════════════
# MAIN
# ════════════════════════════════════════════════════════════════════════════
class _TimeBudgetExceeded(Exception):
    pass


def _summary(title, posted, skipped, failed, wp_enabled):
    logger.info(f"\n{'#'*60}")
    logger.info(f" {title}")
    logger.info(f" ✅ Scraped/Posted : {posted}")
    logger.info(f" ⏭ Skipped        : {skipped}")
    logger.info(f" ❌ Failed         : {failed}")
    logger.info(f" 📄 Full CSV       : {SCRAPED_JOBS_CSV}")
    logger.info(f"{'#'*60}")


def run():
    if os.path.exists(DONE_FLAG_FILE):
        logger.info(f"🏁 {DONE_FLAG_FILE} exists — all locations already scraped. "
                    f"Delete it to force a fresh full re-scrape.")
        return

    wp_enabled = require_wp_config()
    if wp_enabled:
        ensure_job_type_terms()

    _init_scraped_jobs_csv()
    # Union of both trackers: a job already in the CSV or tracker is never redone.
    processed_ids = load_processed_ids() | load_csv_job_ids()
    logger.info(f"📋 {len(processed_ids)} jobs already recorded.")

    locations = get_location_urls()
    if not locations:
        save_progress(0, 1, 0, "", note=f"no locations found — see {DIAG_FILE} / {HOMEPAGE_DEBUG_FILE}")
        logger.error(f"No locations found — aborting. Check {DIAG_FILE}.")
        return

    # ── Resume: prefer matching the saved location URL, fall back to the index ──
    progress = load_progress()
    saved_url = progress.get("location_url", "")
    if saved_url and saved_url in locations:
        start_loc_idx = locations.index(saved_url)
    else:
        start_loc_idx = min(progress.get("location_index", 0), len(locations) - 1)
    start_page = max(1, int(progress.get("page", 1) or 1))

    posted = skipped = failed = 0
    logger.info(f"🚀 Scraping {len(locations)} locations. Resuming at location "
                f"#{start_loc_idx} ({locations[start_loc_idx]}), page {start_page}, "
                f"after position {progress.get('position', 0)}.")

    try:
        for loc_idx in range(start_loc_idx, len(locations)):
            location_url = locations[loc_idx]
            page_num = start_page if loc_idx == start_loc_idx else 1
            consecutive_fetch_failures = 0

            while True:
                if time_budget_exceeded():
                    save_progress(loc_idx, page_num, 0, location_url)
                    raise _TimeBudgetExceeded()

                job_urls = scrape_job_list_page(location_url, page_num)

                if job_urls is None:   # fetch FAILED — don't mistake for "end of location"
                    consecutive_fetch_failures += 1
                    save_progress(loc_idx, page_num, 0, location_url,
                                  note=f"listing fetch failed (x{consecutive_fetch_failures})")
                    if consecutive_fetch_failures >= 3:
                        logger.error("Listing page failed 3 times in a row — stopping this run "
                                     "so the next run resumes at the same page (not skipping it).")
                        raise _TimeBudgetExceeded()
                    time.sleep(5 * consecutive_fetch_failures)
                    continue
                consecutive_fetch_failures = 0

                if not job_urls:
                    logger.info(f"📄 No more jobs at {location_url} (page {page_num}) — next location.")
                    break

                for j, job_url in enumerate(job_urls, start=1):
                    if time_budget_exceeded():
                        save_progress(loc_idx, page_num, j - 1, location_url)
                        raise _TimeBudgetExceeded()

                    logger.info(f"── {location_url} | page {page_num} | job {j}/{len(job_urls)}: {job_url}")
                    job_id = make_job_id(job_url)

                    if job_id in processed_ids:
                        logger.info("⏭ SKIP — already processed.")
                        skipped += 1
                        save_progress(loc_idx, page_num, j, location_url)
                        continue

                    try:
                        job = scrape_job_details(job_url)
                    except Exception as e:
                        logger.error(f"Error scraping job {job_url}: {e}")
                        failed += 1
                        save_progress(loc_idx, page_num, j, location_url)
                        continue

                    if not job:
                        mark_processed(job_id, job_url, "", "skipped_incomplete", location_url, page_num)
                        processed_ids.add(job_id)
                        skipped += 1
                        save_progress(loc_idx, page_num, j, location_url)
                        continue

                    # 1) ALWAYS record the full row in the CSV first.
                    save_job_to_csv(job, page_num, j, job_id)

                    # 2) Optionally push to WordPress.
                    status = "saved_to_csv"
                    if wp_enabled:
                        if job["company_name"]:
                            save_company(job)
                        post_id, post_url = save_job(job, job_id)
                        if post_id:
                            status = f"posted|wp_id={post_id}|{post_url or ''}"
                            logger.info(f"✅ SUCCESS — '{job['job_title']}' → WP ID={post_id} 🔗 {post_url}")
                        else:
                            status = "csv_saved|wp_post_failed"
                            logger.info(f"❌ WordPress post failed (still saved in CSV): {job['job_title']}")
                            failed += 1
                    if not status.endswith("wp_post_failed"):
                        posted += 1

                    mark_processed(job_id, job_url, job["job_title"], status, location_url, page_num)
                    processed_ids.add(job_id)
                    save_progress(loc_idx, page_num, j, location_url)

                    # 3) Commit + push the CSV/trackers to the repo right now.
                    git_push_progress()
                    time.sleep(1)

                save_progress(loc_idx, page_num + 1, 0, location_url)
                logger.info(f"📊 Totals — saved: {posted} | skipped: {skipped} | failed: {failed}")
                page_num += 1

            if loc_idx + 1 < len(locations):
                save_progress(loc_idx + 1, 1, 0, locations[loc_idx + 1])
            else:
                save_progress(loc_idx + 1, 1, 0, "", note="all locations finished")

        _summary(f"✅ FINISHED all {len(locations)} locations "
                 f"({datetime.now().strftime('%Y-%m-%d %H:%M')})", posted, skipped, failed, wp_enabled)
        with open(DONE_FLAG_FILE, "w", encoding="utf-8") as f:
            f.write(f"All {len(locations)} locations fully scraped as of "
                    f"{datetime.now().isoformat()}. Delete this file to force a fresh full re-scrape.")

    except _TimeBudgetExceeded:
        elapsed = time.time() - SCRIPT_START_TIME
        _summary(f"⏱ STOPPED after {elapsed:.0f}s (limit {MAX_RUNTIME_SECONDS}s) — "
                 f"progress saved, next run resumes automatically.", posted, skipped, failed, wp_enabled)

    except KeyboardInterrupt:
        _summary("STOPPED BY USER — re-run to resume from the saved page/position.",
                 posted, skipped, failed, wp_enabled)

    finally:
        # Flush any jobs not yet pushed (matters when GIT_PUSH_EVERY_N_JOBS > 1).
        git_push_progress(force=True)


if __name__ == "__main__":
    logger.info("🚀 Computrabajo Mexico scraper — starting… (Ctrl+C is safe; re-run to resume)")
    run()
    logger.info("✅ Done.")
