"""
Catcher v05.3 — Donma/yanıt vermeme düzeltildi (tamamı arka planda), gelişmiş time‑out + önizleme
===============================================================================================

Bu sürümde ne yeni?
- **UI donması bitti**: Kategori önizleme ve tam tarama artık **arka plan thread**’lerinde.
- **İlerleme/geri bildirim**: Durum yazıları `after()` ile UI’dan güncellenir; butonlar güvenli aç/kapat.
- **Dayanıklı istekler**: `fetch_html` basit **retry + backoff** ve daha sıkı **timeout** kullanır.
- **Aynı UX**: Link Önizleme, filtreler, Excel/CSV çıktıları aynı kaldı.

Kurulum
  pip install requests beautifulsoup4 pandas openpyxl
"""

import os
import re
import json
import time
import queue
import threading
from dataclasses import dataclass, asdict
from typing import List, Dict, Any, Optional, Set, Tuple
from urllib.parse import urljoin, urlparse, urlunparse, parse_qs, urlencode

import requests
import pandas as pd
from bs4 import BeautifulSoup

import tkinter as tk
from tkinter import messagebox, filedialog

# ----------------------------- Sabit çalışma dizini + çıktı ----------------------------- #
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
try:
    os.chdir(BASE_DIR)
except Exception:
    pass
OUTPUT_DIR = os.path.join(BASE_DIR, "output")
os.makedirs(OUTPUT_DIR, exist_ok=True)

# ----------------------------- Genel Ayarlar ----------------------------- #
APP_NAME = "Catcher v05.3"
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
)
HEADERS = {"User-Agent": USER_AGENT, "Accept-Language": "tr-TR,tr;q=0.9,en;q=0.8"}
REQ_TIMEOUT = (6, 18)  # (connect, read) saniye
MAX_RETRIES = 2        # toplam deneme: 1+MAX_RETRIES

DEFAULT_MAX_PAGES = 20
DEFAULT_MAX_PRODUCTS = 1000

MATERIAL_DICT = [
    "pamuk", "keten", "bambu", "viskon", "polyester", "ipek", "şifon", "saten", "modal",
    "akrilik", "naylon", "elastan", "likra", "kaşmir", "yün", "tencel", "rayon",
    "cotton", "linen", "bamboo", "viscose", "polyester", "silk", "chiffon", "satin", "modal",
    "acrylic", "nylon", "elastane", "spandex", "cashmere", "wool", "lyocell", "rayon",
]
COLOR_HINTS = ["renk", "color", "colours", "colors", "tone", "ton", "shade", "hue"]
SIZE_HINTS = ["boyut", "ölçü", "size", "dimension", "uzunluk", "eni", "cm", "mm"]

EXCLUDE_REGION_SELECTORS = [
    "header", "footer", "nav",
    "div[id*='header']", "div[class*='header']",
    "div[id*='footer']", "div[class*='footer']",
]
EXCLUDE_CLASSES = [
    "swatch", "variant", "varian", "renk", "color", "option", "attribute", "thumb-variant",
    "icon", "logo", "avatar", "badge", "placeholder"
]
IMG_EXT_ALLOW = (".jpg", ".jpeg", ".png", ".webp")

@dataclass
class Product:
    url: str
    title: Optional[str] = None
    colors: Optional[str] = None
    sizes: Optional[str] = None
    material: Optional[str] = None
    material_ratio: Optional[str] = None
    price: Optional[str] = None
    currency: Optional[str] = None
    sku: Optional[str] = None
    brand: Optional[str] = None
    image_urls: Optional[str] = None
    raw_note: Optional[str] = None

# ----------------------------- HTTP + Yardımcılar ----------------------------- #
_session = requests.Session()


def fetch_html(url: str) -> Optional[str]:
    for attempt in range(MAX_RETRIES + 1):
        try:
            resp = _session.get(url, headers=HEADERS, timeout=REQ_TIMEOUT)
            if resp.status_code == 200 and resp.text:
                return resp.text
        except Exception:
            pass
        # küçük backoff
        time.sleep(0.6 * (attempt + 1))
    return None


def parse_json_ld(soup: BeautifulSoup) -> Dict[str, Any]:
    data: Dict[str, Any] = {}
    scripts = soup.find_all("script", type=lambda t: t and "ld+json" in t)
    for sc in scripts:
        try:
            txt = sc.string or sc.text
            blob = json.loads(txt)
        except Exception:
            continue
        candidates = blob if isinstance(blob, list) else [blob]
        for item in candidates:
            if not isinstance(item, dict):
                continue
            t = item.get("@type")
            if t == "Product" or (isinstance(t, list) and "Product" in t):
                data.update(item)
                return data
    return data


def text_or_none(x: Any) -> Optional[str]:
    if x is None:
        return None
    if isinstance(x, (list, tuple)):
        try:
            return "; ".join([str(i) for i in x if i])
        except Exception:
            return str(x)
    return str(x).strip() or None


def find_meta(soup: BeautifulSoup, names: List[str]) -> Optional[str]:
    for n in names:
        tag = soup.find("meta", attrs={"property": n}) or soup.find("meta", attrs={"name": n})
        if tag and tag.get("content"):
            return tag["content"].strip()
    return None

# ----------------------------- Link sezgisi + sayfalama ----------------------------- #
PRODUCT_PATH_HINTS = [
    "/urun/", "/product", "/products/", "/p-", "/item/", "/detail", "/detay", "/shop/",
    "/collections/", "/collection/", "/catalog/", "/kategori/", "/category/"
]
CONTENT_SCOPES = [
    "main a", "div[id*='main'] a", "div[class*='main'] a",
    "div[id*='content'] a", "div[class*='content'] a",
    "div[class*='listing'] a", "div[class*='grid'] a",
    "div[class*='product'] a", "section[class*='product'] a",
    "ul[class*='product'] a", "ol[class*='product'] a",
    "div[class*='catalog'] a", "div[class*='collection'] a",
]


def domain_from(url: str) -> str:
    try:
        return urlparse(url).netloc.lower()
    except Exception:
        return ""


def extract_links_in_scopes(soup: BeautifulSoup, page_url: str) -> List[str]:
    excluded_nodes = set()
    for sel in EXCLUDE_REGION_SELECTORS:
        for node in soup.select(sel):
            excluded_nodes.add(node)

    def is_inside_excluded(a_tag) -> bool:
        parent = a_tag.parent
        while parent is not None:
            if parent in excluded_nodes or parent.name in ("header", "footer", "nav"):
                return True
            parent = parent.parent
        return False

    links: List[str] = []
    for scope in CONTENT_SCOPES:
        for a in soup.select(scope):
            href = a.get("href")
            if not href:
                continue
            if is_inside_excluded(a):
                continue
            full = urljoin(page_url, href)
            links.append(full)
    return links


def looks_like_product_url(u: str) -> bool:
    path = urlparse(u).path.lower()
    if any(h in path for h in PRODUCT_PATH_HINTS):
        return True
    segs = [s for s in path.split('/') if s]
    if segs:
        last = segs[-1]
        if len(last) >= 6 and ("-" in last or any(ch.isdigit() for ch in last)):
            return True
    return False


def parse_filters(s: str) -> List[str]:
    return [x.strip() for x in s.split(";") if x.strip()]


def filter_links(links: List[str], domain: str, include_filter: str, exclude_filter: str) -> List[str]:
    links = [u for u in links if domain_from(u) == domain]
    inc = parse_filters(include_filter)
    exc = parse_filters(exclude_filter)

    def ok(u: str) -> bool:
        if inc and not any(s in u for s in inc):
            return False
        if exc and any(s in u for s in exc):
            return False
        if not inc and not looks_like_product_url(u):
            return False
        return True

    uniq: List[str] = []
    for u in links:
        if u not in uniq and ok(u):
            uniq.append(u)
    return uniq


def next_by_rel_or_class(soup: BeautifulSoup, page_url: str) -> Optional[str]:
    tag = soup.find("link", rel=lambda v: v and "next" in v)
    if tag and tag.get("href"):
        return urljoin(page_url, tag["href"])
    tag = soup.find("a", attrs={"rel": "next"})
    if tag and tag.get("href"):
        return urljoin(page_url, tag["href"])
    tag = soup.find("a", string=lambda t: t and t.strip().lower() in ["sonraki", "next", ">", "»"])
    if tag and tag.get("href"):
        return urljoin(page_url, tag["href"])
    tag = soup.find("a", class_=lambda c: c and re.search(r"next|sonraki|pagination__next|page-next", c.lower()))
    if tag and tag.get("href"):
        return urljoin(page_url, tag["href"])
    return None


def all_numbered_pages(soup: BeautifulSoup, page_url: str) -> List[str]:
    pages: List[str] = []
    for a in soup.select("a[href]"):
        txt = (a.get_text(strip=True) or "").lower()
        if txt.isdigit():
            pages.append(urljoin(page_url, a["href"]))
    uniq = []
    for u in pages:
        if u not in uniq:
            uniq.append(u)
    return uniq


def bump_page_param(url: str) -> Optional[str]:
    pr = urlparse(url)
    qs = parse_qs(pr.query)
    if "page" in qs:
        try:
            cur = int(qs["page"][0])
            qs["page"] = [str(cur + 1)]
            new_query = urlencode({k: v[0] if isinstance(v, list) else v for k, v in qs.items()})
            return urlunparse((pr.scheme, pr.netloc, pr.path, pr.params, new_query, pr.fragment))
        except Exception:
            return None
    return None

# ----------------------------- Görsel çıkarımı ----------------------------- #

def is_excluded_by_class(tag) -> bool:
    classes = tag.get("class") or []
    classes_low = [c.lower() for c in classes]
    return any(any(ex in c for ex in EXCLUDE_CLASSES) for c in classes_low)


def find_gallery_containers(soup: BeautifulSoup) -> List[Any]:
    candidates = []
    for tag in soup.find_all(["div", "section", "ul", "ol"]):
        try:
            idtxt = (tag.get("id") or "").lower()
            clstxt = " ".join((tag.get("class") or [])).lower()
            if re.search(r"product|urun", idtxt + " " + clstxt) and \
               re.search(r"gallery|media|images|slider|carousel|thumbs|zoom|fotorama|swiper", idtxt + " " + clstxt):
                if not is_excluded_by_class(tag):
                    candidates.append(tag)
        except Exception:
            continue
    return candidates


def extract_product_images(soup: BeautifulSoup, base_url: str) -> List[str]:
    urls: List[str] = []

    ld = parse_json_ld(soup)
    if ld.get("image"):
        imgs = ld["image"] if isinstance(ld["image"], list) else [ld["image"]]
        for u in imgs:
            if isinstance(u, dict) and u.get("url"):
                urls.append(urljoin(base_url, u["url"]))
            elif isinstance(u, str):
                urls.append(urljoin(base_url, u))

    galleries = find_gallery_containers(soup)
    for gal in galleries:
        for img in gal.find_all("img"):
            src = img.get("data-src") or img.get("data-large_image") or img.get("src")
            if not src:
                continue
            full = urljoin(base_url, src)
            if is_excluded_by_class(img):
                continue
            alt = (img.get("alt") or "").lower()
            if any(k in alt for k in ["swatch", "variant", "renk", "color", "logo", "icon"]):
                continue
            if len(full) < 6:
                continue
            urls.append(full)

    if not urls:
        for img in soup.find_all("img"):
            if is_excluded_by_class(img):
                continue
            src = img.get("data-src") or img.get("data-large_image") or img.get("src")
            if not src:
                continue
            full = urljoin(base_url, src)
            alt = (img.get("alt") or "").lower()
            if any(k in alt for k in ["swatch", "variant", "renk", "color", "logo", "icon"]):
                continue
            urls.append(full)

    uniq: List[str] = []
    for u in urls:
        if u and u not in uniq:
            uniq.append(u)
    return uniq[:30]

# ----------------------------- Ürün ayrıştırma ----------------------------- #

def infer_colors(text: str) -> Optional[str]:
    lines = [ln.strip() for ln in re.split(r"[\n\r\.\-•]", text) if ln.strip()]
    hits = []
    for ln in lines:
        if any(h in ln.lower() for h in COLOR_HINTS):
            hits.append(ln)
    return "; ".join(dict.fromkeys(hits)) or None


def infer_sizes(text: str) -> Optional[str]:
    lines = [ln.strip() for ln in re.split(r"[\n\r]", text) if ln.strip()]
    hits = []
    for ln in lines:
        if any(h in ln.lower() for h in SIZE_HINTS):
            hits.append(ln)
    dims = re.findall(r"\b(\d{2,3})\s*[x×]\s*(\d{2,3})\b", text.lower())
    if dims:
        hits.append("; ".join(["x".join(d) for d in dims]))
    return "; ".join(dict.fromkeys(hits)) or None


def infer_material(text: str) -> Tuple[Optional[str], Optional[str]]:
    text_low = text.lower()
    mats = [m for m in MATERIAL_DICT if m in text_low]
    mats = list(dict.fromkeys(mats))
    ratio_hits = re.findall(r"%(?:\s*)?(\d{1,3})", text)
    ratio = ", ".join([f"%{r}" for r in ratio_hits]) if ratio_hits else None
    mat = ", ".join(mats) if mats else None
    return mat or None, ratio


def scrape_product(url: str) -> Product:
    html = fetch_html(url)
    if not html:
        return Product(url=url, raw_note="HTML alınamadı")
    soup = BeautifulSoup(html, "html.parser")

    prod = Product(url=url)

    ld = parse_json_ld(soup)
    if ld:
        prod.title = text_or_none(ld.get("name")) or prod.title
        if isinstance(ld.get("brand"), dict):
            prod.brand = text_or_none(ld.get("brand", {}).get("name")) or prod.brand
        else:
            prod.brand = text_or_none(ld.get("brand")) or prod.brand
        offers = ld.get("offers")
        if isinstance(offers, dict):
            prod.price = text_or_none(offers.get("price"))
            prod.currency = text_or_none(offers.get("priceCurrency"))
        prod.sku = text_or_none(ld.get("sku")) or prod.sku
        prod.colors = text_or_none(ld.get("color")) or prod.colors
        prod.sizes = text_or_none(ld.get("size")) or prod.sizes
        mat_field = text_or_none(ld.get("material"))
        if mat_field:
            prod.material = mat_field
        imgs = ld.get("image")
        if imgs:
            if isinstance(imgs, list):
                prod.image_urls = "; ".join([urljoin(url, i if isinstance(i, str) else i.get("url", "")) for i in imgs])
            elif isinstance(imgs, str):
                prod.image_urls = urljoin(url, imgs)

    if not prod.title:
        tag = soup.find("h1") or soup.find("h2")
        prod.title = text_or_none(tag.text if tag else None) or find_meta(soup, ["og:title", "twitter:title"]) or None

    text_blob = "\n".join([t.get_text(" ", strip=True) for t in soup.find_all(["p", "li", "td", "div"])])
    if not prod.colors:
        prod.colors = infer_colors(text_blob)
    if not prod.sizes:
        prod.sizes = infer_sizes(text_blob)
    if not prod.material:
        mat, ratio = infer_material(text_blob)
        prod.material = mat
        prod.material_ratio = ratio

    if not prod.price:
        price_meta = find_meta(soup, ["product:price:amount", "og:price:amount"]) or None
        prod.price = price_meta
    if not prod.currency:
        currency_meta = find_meta(soup, ["product:price:currency", "og:price:currency"]) or None
        prod.currency = currency_meta

    imgs = extract_product_images(soup, url)
    if imgs:
        prod.image_urls = "; ".join(imgs)

    if not any([prod.title, prod.price, prod.material, prod.colors, prod.sizes]):
        prod.raw_note = "Veri kısıtlı olabilir; site JS ile render ediyor olabilir."

    return prod

# ----------------------------- Kategori Gezinimi ----------------------------- #

def extract_product_links_from_category(cat_url: str, max_pages: int, max_products: int, include_filter: str, exclude_filter: str) -> List[str]:
    seen: Set[str] = set()
    results: List[str] = []
    page_url = cat_url
    pages = 0
    dom = domain_from(cat_url)

    while page_url and pages < max_pages and len(results) < max_products:
        html = fetch_html(page_url)
        if not html:
            break
        soup = BeautifulSoup(html, "html.parser")

        all_links = extract_links_in_scopes(soup, page_url)
        filtered = filter_links(all_links, dom, include_filter, exclude_filter)

        for u in filtered:
            if u in seen:
                continue
            seen.add(u)
            results.append(u)
            if len(results) >= max_products:
                break

        if len(results) >= max_products:
            break

        nxt = next_by_rel_or_class(soup, page_url)
        if not nxt:
            pages_urls = all_numbered_pages(soup, page_url)
            pages_urls = [p for p in pages_urls if p != page_url]
            if pages_urls:
                nxt = pages_urls[0]
        if not nxt:
            bump = bump_page_param(page_url)
            if bump and bump != page_url:
                nxt = bump
        page_url = nxt
        pages += 1

    return results[:max_products]

# ----------------------------- Worker / Threading ----------------------------- #

class ScrapeWorker(threading.Thread):
    def __init__(self, in_q: queue.Queue, out_list: List[Product]):
        super().__init__(daemon=True)
        self.in_q = in_q
        self.out_list = out_list

    def run(self):
        while True:
            try:
                url = self.in_q.get(timeout=0.1)
            except queue.Empty:
                break
            try:
                prod = scrape_product(url)
                self.out_list.append(prod)
            finally:
                self.in_q.task_done()

# ----------------------------- GUI ----------------------------- #

class App:
    def __init__(self, root: tk.Tk):
        self.root = root
        root.title(f"{APP_NAME} — Çok Alanlı Toplayıcı")
        root.geometry("980x760")

        mode_frame = tk.Frame(root)
        mode_frame.pack(fill=tk.X, padx=10, pady=6)
        self.mode = tk.StringVar(value="category")
        tk.Radiobutton(mode_frame, text="Ürün URL listesi", variable=self.mode, value="list").pack(side=tk.LEFT)
        tk.Radiobutton(mode_frame, text="Kategori URL", variable=self.mode, value="category").pack(side=tk.LEFT, padx=12)

        self.lbl = tk.Label(root, text="Mod: Kategori URL — İlk satıra tek bir kategori URL'si gir. Gerekirse filtreleri kullan.")
        self.lbl.pack(pady=4)

        self.txt = tk.Text(root, height=14)
        self.txt.pack(fill=tk.BOTH, expand=True, padx=10)

        cat_frame = tk.Frame(root)
        cat_frame.pack(fill=tk.X, padx=10, pady=6)

        tk.Label(cat_frame, text="Max Sayfa:").grid(row=0, column=0, sticky="w")
        self.ent_pages = tk.Entry(cat_frame, width=6)
        self.ent_pages.insert(0, str(DEFAULT_MAX_PAGES))
        self.ent_pages.grid(row=0, column=1, padx=6)

        tk.Label(cat_frame, text="Max Ürün:").grid(row=0, column=2, sticky="w")
        self.ent_products = tk.Entry(cat_frame, width=8)
        self.ent_products.insert(0, str(DEFAULT_MAX_PRODUCTS))
        self.ent_products.grid(row=0, column=3, padx=6)

        tk.Label(cat_frame, text="Dahil Et (substring; ; ile ayır):").grid(row=1, column=0, sticky="w", pady=4)
        self.ent_include = tk.Entry(cat_frame, width=46)
        self.ent_include.insert(0, "")
        self.ent_include.grid(row=1, column=1, columnspan=3, sticky="we")

        tk.Label(cat_frame, text="Hariç Tut (substring; ; ile ayır):").grid(row=2, column=0, sticky="w")
        self.ent_exclude = tk.Entry(cat_frame, width=46)
        self.ent_exclude.insert(0, "")
        self.ent_exclude.grid(row=2, column=1, columnspan=3, sticky="we")

        btn_frame = tk.Frame(root)
        btn_frame.pack(fill=tk.X, pady=8)
        self.btn_preview = tk.Button(btn_frame, text="Linkleri Önizle", command=self.on_preview)
        self.btn_preview.pack(side=tk.LEFT, padx=10)
        self.btn_run = tk.Button(btn_frame, text="Çalıştır ve Excel'e Yaz", command=self.on_run)
        self.btn_run.pack(side=tk.LEFT, padx=10)
        self.btn_save_as = tk.Button(btn_frame, text="Çıktı Klasörü Seç", command=self.choose_dir)
        self.btn_save_as.pack(side=tk.LEFT)

        self.status = tk.Label(root, text="Hazır.")
        self.status.pack(anchor="w", padx=10, pady=4)

        self.output_dir = OUTPUT_DIR
        os.makedirs(self.output_dir, exist_ok=True)

        self.mode.trace_add('write', self.on_mode_change)

    # ---- UI yardımcıları ---- #
    def set_status(self, text: str):
        self.status.config(text=text)
        self.root.update_idletasks()

    def on_mode_change(self, *args):
        if self.mode.get() == "list":
            self.lbl.config(text="Mod: Ürün URL listesi — Her satıra bir ürün URL'si yapıştır (en fazla 100). İlk satır zorunlu.")
        else:
            self.lbl.config(text="Mod: Kategori URL — İlk satıra tek bir kategori URL'si gir. Gerekirse filtreleri kullan.")

    def choose_dir(self):
        d = filedialog.askdirectory(initialdir=self.output_dir or OUTPUT_DIR)
        if d:
            self.output_dir = d
            self.set_status(f"Çıktı: {self.output_dir}")

    # ---- Önizleme (arka plan) ---- #
    def on_preview(self):
        if self.mode.get() != "category":
            messagebox.showinfo("Bilgi", "Önizleme yalnızca Kategori URL modunda çalışır.")
            return
        raw = self.txt.get("1.0", tk.END).strip()
        lines = [u.strip() for u in raw.splitlines() if u.strip()]
        if not lines:
            messagebox.showerror("Hata", "İlk satıra kategori URL'si gir.")
            return
        cat_url = lines[0]
        self.btn_preview.config(state=tk.DISABLED)
        self.set_status("Kategori linkleri toplanıyor (önizleme)…")

        def worker():
            try:
                links = self.collect_category_links(cat_url)
            except Exception:
                links = []
            def show():
                self.btn_preview.config(state=tk.NORMAL)
                if not links:
                    messagebox.showerror("Önizleme", "Hiç ürün linki bulunamadı. Filtreleri gevşetmeyi deneyin.")
                    self.set_status("Hazır.")
                    return
                top = tk.Toplevel(self.root)
                top.title("Bulunan Ürün Linkleri")
                text = tk.Text(top, height=24, width=110)
                text.pack(fill=tk.BOTH, expand=True)
                text.insert("1.0", "\n".join(links))
                self.set_status(f"Önizleme: {len(links)} link bulundu")
            self.root.after(0, show)
        threading.Thread(target=worker, daemon=True).start()

    # ---- Çalıştır (arka plan) ---- #
    def on_run(self):
        raw = self.txt.get("1.0", tk.END).strip()
        lines = [u.strip() for u in raw.splitlines() if u.strip()]
        if not lines:
            messagebox.showerror("Hata", "En az 1 satır girmelisin.")
            return

        mode = self.mode.get()
        urls: List[str] = []

        if mode == "list":
            urls = lines[:200]
        else:
            cat_url = lines[0]
            self.btn_run.config(state=tk.DISABLED)
            self.set_status("Kategori taranıyor, linkler toplanıyor…")
            # Link toplama da arka planda
            def collect_then_run():
                try:
                    u = self.collect_category_links(cat_url)
                except Exception:
                    u = []
                def next_step():
                    if not u:
                        self.btn_run.config(state=tk.NORMAL)
                        messagebox.showerror("Hata", "Kategori altında uygun ürün linki bulunamadı.")
                        self.set_status("Hazır.")
                        return
                    self._run_with_urls(u)
                self.root.after(0, next_step)
            threading.Thread(target=collect_then_run, daemon=True).start()
            return

        # Liste modunda doğrudan çalıştır
        self._run_with_urls(urls)

    def _run_with_urls(self, urls: List[str]):
        self.btn_run.config(state=tk.DISABLED)
        self.set_status(f"Toplam {len(urls)} URL işleniyor…")

        in_q: queue.Queue = queue.Queue()
        for u in urls:
            in_q.put(u)

        results: List[Product] = []
        workers = [ScrapeWorker(in_q, results) for _ in range(min(12, len(urls)))]

        def background():
            for w in workers:
                w.start()
            in_q.join()
            rows = [asdict(p) for p in results]
            df = pd.DataFrame(rows)
            ts = time.strftime("%Y%m%d_%H%M%S")
            suffix = "catcher_v05_3"
            xlsx_path = os.path.join(self.output_dir, f"sehrazat_scrape_{suffix}_{ts}.xlsx")
            csv_path = os.path.join(self.output_dir, f"sehrazat_scrape_{suffix}_{ts}.csv")
            err1 = err2 = None
            try:
                with pd.ExcelWriter(xlsx_path, engine="openpyxl") as writer:
                    df.to_excel(writer, index=False, sheet_name="products")
            except Exception as e:
                err1 = str(e)
            try:
                df.to_csv(csv_path, index=False)
            except Exception as e:
                err2 = str(e)

            def finalize():
                self.btn_run.config(state=tk.NORMAL)
                if err1:
                    messagebox.showerror("Excel hatası", f"Excel yazılamadı: {err1}")
                if err2:
                    messagebox.showerror("CSV hatası", f"CSV yazılamadı: {err2}")
                self.set_status(f"Bitti. Kayıt: {xlsx_path}")
                messagebox.showinfo("Tamam", f"İşlem tamamlandı.\nExcel: {xlsx_path}\nCSV: {csv_path}")
            self.root.after(0, finalize)

        threading.Thread(target=background, daemon=True).start()

    # Ortak yardımcılar
    def collect_category_links(self, cat_url: str) -> List[str]:
        try:
            max_pages = max(1, int(self.ent_pages.get()))
        except Exception:
            max_pages = DEFAULT_MAX_PAGES
        try:
            max_products = max(1, int(self.ent_products.get()))
        except Exception:
            max_products = DEFAULT_MAX_PRODUCTS
        include_filter = self.ent_include.get().strip()
        exclude_filter = self.ent_exclude.get().strip()
        return extract_product_links_from_category(cat_url, max_pages, max_products, include_filter, exclude_filter)

# ----------------------------- Giriş Noktası ----------------------------- #

def main():
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()

# ---------------------------------------------------------------
# Ek: run_catcher.bat — aynı klasöre kaydet
# ---------------------------------------------------------------
# @echo off
# setlocal ENABLEDELAYEDEXPANSION
# pushd "%~dp0"
# python --version >nul 2>&1
# IF ERRORLEVEL 1 (
#     py -3 --version >nul 2>&1
#     IF ERRORLEVEL 1 (
#         echo [HATA] Python bulunamadi. https://www.python.org/downloads/
#         pause
#         exit /b 1
#     ) ELSE (
#         set PY_CMD=py -3
#     )
# ) ELSE (
#     set PY_CMD=python
# )
# echo Gerekli kutuphaneler kuruluyor...
# %PY_CMD% -m pip install --quiet requests beautifulsoup4 pandas openpyxl
# set SCRIPT=catcher_v05_3.py
# if not exist "%SCRIPT%" (
#   echo [HATA] %SCRIPT% bulunamadi. Bu klasorde mevcut .py dosyalari:
#   dir /b *.py
#   pause
#   exit /b 1
# )
# echo ---------------------------------------------
# echo  %SCRIPT% baslatiliyor...
# echo ---------------------------------------------
# %PY_CMD% "%SCRIPT%"
# echo ---------------------------------------------
# echo  Program bitti.
# echo ---------------------------------------------
# pause
# popd
