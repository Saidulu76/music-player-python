import os
import random
import heapq
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from dataclasses import dataclass
from typing import Optional, List, Dict
import pygame


# -----------------------------
# ---------- DSA --------------
# -----------------------------

@dataclass
class Node:
    """Doubly linked list node for a song."""
    title: str
    path: str
    prev: Optional['Node'] = None
    next: Optional['Node'] = None


class DoublyLinkedList:
    """Playlist as a doubly linked list for efficient next/prev navigation."""
    def __init__(self):
        self.head: Optional[Node] = None
        self.tail: Optional[Node] = None
        self.size = 0

    def append(self, title: str, path: str) -> Node:
        node = Node(title, path)
        if self.tail is None:
            self.head = self.tail = node
        else:
            node.prev = self.tail
            self.tail.next = node
            self.tail = node
        self.size += 1
        return node

    def clear(self):
        self.head = self.tail = None
        self.size = 0

    def to_list(self) -> List[Node]:
        out = []
        cur = self.head
        while cur:
            out.append(cur)
            cur = cur.next
        return out

    def from_nodes(self, nodes: List[Node]):
        """Rebuild DLL from a list of nodes in order."""
        self.clear()
        prev = None
        for n in nodes:
            # detach n
            n.prev = n.next = None
            if self.head is None:
                self.head = n
            if prev is not None:
                prev.next = n
                n.prev = prev
            prev = n
        self.tail = prev
        self.size = len(nodes)


class TrieNode:
    def __init__(self):
        self.children: Dict[str, 'TrieNode'] = {}
        self.ends: List[str] = []  # store titles completing here (could store indices)

class Trie:
    """Prefix search for song titles."""
    def __init__(self):
        self.root = TrieNode()

    def insert(self, word: str):
        node = self.root
        for ch in word.lower():
            if ch not in node.children:
                node.children[ch] = TrieNode()
            node = node.children[ch]
        # store at leaf (cap list to avoid growth)
        if word not in node.ends:
            node.ends.append(word)
            if len(node.ends) > 20:
                node.ends.pop(0)

    def prefix_search(self, prefix: str, limit: int = 20) -> List[str]:
        node = self.root
        for ch in prefix.lower():
            if ch not in node.children:
                return []
            node = node.children[ch]
        # Collect words under this node (BFS, capped)
        results = []
        q = [(node, prefix)]
        while q and len(results) < limit:
            n, _ = q.pop(0)
            results.extend(n.ends)
            for ch, child in n.children.items():
                q.append((child, prefix + ch))
        # dedupe while preserving order
        seen = set()
        out = []
        for w in results:
            if w not in seen:
                out.append(w)
                seen.add(w)
            if len(out) >= limit:
                break
        return out


# -----------------------------
# ------- Music Engine --------
# -----------------------------

AUDIO_EXTS = (".mp3", ".wav", ".ogg")

class MusicEngine:
    """Wrapper around pygame.mixer.music with simple state."""
    def __init__(self):
        pygame.mixer.init()
        self.volume = 0.7
        pygame.mixer.music.set_volume(self.volume)
        self.paused = False

    def load_and_play(self, path: str):
        pygame.mixer.music.load(path)
        pygame.mixer.music.play()
        self.paused = False

    def pause(self):
        pygame.mixer.music.pause()
        self.paused = True

    def resume(self):
        pygame.mixer.music.unpause()
        self.paused = False

    def stop(self):
        pygame.mixer.music.stop()
        self.paused = False

    def set_volume(self, v: float):
        self.volume = max(0.0, min(1.0, v))
        pygame.mixer.music.set_volume(self.volume)

    def is_busy(self) -> bool:
        return pygame.mixer.music.get_busy()


# -----------------------------
# --------- GUI App -----------
# -----------------------------

class MusicPlayerApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Python DSA Music Player")
        self.geometry("980x620")
        self.minsize(840, 540)

        # DSA structures
        self.dll = DoublyLinkedList()
        self.history_stack: List[Node] = []          # back stack
        self.play_counts: Dict[str, int] = {}        # title -> count (for heap)
        self.trie = Trie()
        self.shuffle_on = False

        self.current: Optional[Node] = None
        self.node_by_title: Dict[str, Node] = {}     # fast lookup

        self.engine = MusicEngine()

        self._build_ui()
        self._poll_playback()  # start polling loop (auto-next)

        # Keyboard shortcuts
        self.bind("<space>", lambda e: self._toggle_pause())
        self.bind("<Right>", lambda e: self.next_song())
        self.bind("<Left>", lambda e: self.prev_song())
        self.bind("<Control-f>", lambda e: (self.search_entry.focus_set(), self.search_entry.select_range(0, tk.END)))
        self.bind("<Control-o>", lambda e: self.load_folder())
        self.bind("<Control-s>", lambda e: self._toggle_shuffle())

    # ---------- UI ----------
    def _build_ui(self):
        # Top toolbar
        top = ttk.Frame(self, padding=8)
        top.pack(side=tk.TOP, fill=tk.X)

        self.folder_btn = ttk.Button(top, text="📂 Load Folder", command=self.load_folder)
        self.folder_btn.pack(side=tk.LEFT, padx=(0, 8))

        self.play_btn = ttk.Button(top, text="▶️ Play", command=self.play_selected)
        self.play_btn.pack(side=tk.LEFT)
        self.pause_btn = ttk.Button(top, text="⏸️ Pause", command=self._toggle_pause)
        self.pause_btn.pack(side=tk.LEFT, padx=4)
        self.stop_btn = ttk.Button(top, text="⏹️ Stop", command=self.stop_song)
        self.stop_btn.pack(side=tk.LEFT)

        self.prev_btn = ttk.Button(top, text="⏮️ Prev", command=self.prev_song)
        self.prev_btn.pack(side=tk.LEFT, padx=(16, 4))
        self.next_btn = ttk.Button(top, text="⏭️ Next", command=self.next_song)
        self.next_btn.pack(side=tk.LEFT)

        self.shuffle_btn = ttk.Checkbutton(top, text="🔀 Shuffle (Ctrl+S)", command=self._toggle_shuffle)
        self.shuffle_var = tk.BooleanVar(value=False)
        self.shuffle_btn.config(variable=self.shuffle_var)
        self.shuffle_btn.pack(side=tk.LEFT, padx=(16, 4))

        ttk.Label(top, text="🔊").pack(side=tk.LEFT, padx=(16, 4))
        self.volume = tk.DoubleVar(value=70)
        self.volume_scale = ttk.Scale(top, from_=0, to=100, variable=self.volume, command=self._on_volume_change, length=160)
        self.volume_scale.pack(side=tk.LEFT)

        ttk.Button(top, text="⭐ Top Played", command=self.show_top_played).pack(side=tk.RIGHT)

        # Search + suggestions
        search_frame = ttk.Frame(self, padding=(8, 0))
        search_frame.pack(fill=tk.X)
        ttk.Label(search_frame, text="Search (prefix):").pack(side=tk.LEFT)
        self.search_entry = ttk.Entry(search_frame)
        self.search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=8)
        self.search_entry.bind("<KeyRelease>", self._on_search_change)
        self.search_entry.bind("<Return>", self._go_to_first_suggestion)

        self.suggest_list = tk.Listbox(self, height=6)
        self.suggest_list.pack(fill=tk.X, padx=8, pady=(2, 8))
        self.suggest_list.bind("<Double-Button-1>", self._choose_suggestion)

        # Playlist + now playing
        middle = ttk.Frame(self, padding=8)
        middle.pack(fill=tk.BOTH, expand=True)

        left = ttk.Frame(middle)
        left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        ttk.Label(left, text="Playlist").pack(anchor="w")
        self.playlist = tk.Listbox(left, selectmode=tk.SINGLE)
        self.playlist.pack(fill=tk.BOTH, expand=True)
        self.playlist.bind("<Double-Button-1>", lambda e: self.play_selected())

        right = ttk.Frame(middle, width=280)
        right.pack(side=tk.RIGHT, fill=tk.Y)
        right.pack_propagate(False)

        ttk.Label(right, text="Now Playing").pack(anchor="w")
        self.now_label = ttk.Label(right, text="—", font=("Segoe UI", 12))
        self.now_label.pack(anchor="w", pady=(0, 12))

        info = ttk.Label(
            right,
            text=(
                "Tips:\n"
                "• Double-click a song to play\n"
                "• Space: Pause/Resume\n"
                "• ← / → : Prev / Next\n"
                "• Ctrl+O: Load Folder\n"
                "• Ctrl+F: Focus Search\n"
                "• Ctrl+S: Toggle Shuffle\n"
            ),
            justify=tk.LEFT
        )
        info.pack(anchor="w", pady=(12, 0))

        # Status bar
        self.status = ttk.Label(self, text="Load a folder to begin…", relief=tk.SUNKEN, anchor="w")
        self.status.pack(side=tk.BOTTOM, fill=tk.X)

    # ---------- Folder / Playlist ----------
    def load_folder(self):
        folder = filedialog.askdirectory(title="Select folder with audio files")
        if not folder:
            return

        files = [os.path.join(folder, f) for f in os.listdir(folder)]
        songs = [(os.path.splitext(os.path.basename(p))[0], p) for p in files if p.lower().endswith(AUDIO_EXTS)]

        if not songs:
            messagebox.showinfo("No audio", "No .mp3/.wav/.ogg files found in this folder.")
            return

        # Reset DSA
        self.engine.stop()
        self.dll.clear()
        self.history_stack.clear()
        self.trie = Trie()
        self.node_by_title.clear()
        self.current = None
        self.playlist.delete(0, tk.END)
        self.suggest_list.delete(0, tk.END)

        # Fill data structures
        nodes = []
        for title, path in sorted(songs, key=lambda x: x[0].lower()):
            node = self.dll.append(title, path)
            self.trie.insert(title)
            self.node_by_title[title] = node
            nodes.append(node)
            self.playlist.insert(tk.END, title)

        self.status.config(text=f"Loaded {len(nodes)} songs")
        self.now_label.config(text="—")

    # ---------- Playback ----------
    def play_node(self, node: Node):
        if node is None:
            return
        try:
            self.engine.load_and_play(node.path)
        except Exception as e:
            messagebox.showerror("Playback error", str(e))
            return
        # Update counts (for heap)
        self.play_counts[node.title] = self.play_counts.get(node.title, 0) + 1
        # Update current and UI
        self.current = node
        self.now_label.config(text=node.title)
        self._select_in_listbox(node.title)
        self.status.config(text=f"Playing: {node.title}")

    def play_selected(self):
        sel = self.playlist.curselection()
        if not sel:
            # If nothing selected, play first item
            title = self.playlist.get(0) if self.playlist.size() > 0 else None
        else:
            title = self.playlist.get(sel[0])

        if not title:
            return

        node = self.node_by_title.get(title)
        if node is None:
            return

        # push current to history if moving
        if self.current and self.current is not node:
            self.history_stack.append(self.current)

        self.play_node(node)

    def _toggle_pause(self):
        if self.engine.is_busy() and not self.engine.paused:
            self.engine.pause()
            self.status.config(text="Paused")
        else:
            self.engine.resume()
            self.status.config(text="Resumed")

    def stop_song(self):
        self.engine.stop()
        self.status.config(text="Stopped")

    def next_song(self):
        nxt = None
        if self.shuffle_on:
            nxt = self._random_next()
        else:
            nxt = self.current.next if self.current else self.dll.head

        if nxt:
            if self.current:
                self.history_stack.append(self.current)
            self.play_node(nxt)
        else:
            self.status.config(text="End of playlist")

    def prev_song(self):
        if self.history_stack:
            prev = self.history_stack.pop()
            self.play_node(prev)
        else:
            self.status.config(text="No previous song")

    def _random_next(self) -> Optional[Node]:
        # Pick a random neighbor excluding current; still push history for back-nav
        nodes = self.dll.to_list()
        if not nodes:
            return None
        if self.current is None:
            return random.choice(nodes)
        if len(nodes) == 1:
            return None
        choices = [n for n in nodes if n is not self.current]
        return random.choice(choices) if choices else None

    def _on_volume_change(self, _):
        self.engine.set_volume(self.volume.get() / 100.0)

    # ---------- Search (Trie) ----------
    def _on_search_change(self, _event):
        q = self.search_entry.get().strip()
        self.suggest_list.delete(0, tk.END)
        if not q:
            return
        suggestions = self.trie.prefix_search(q, limit=30)
        for s in suggestions:
            self.suggest_list.insert(tk.END, s)

    def _choose_suggestion(self, _event):
        sel = self.suggest_list.curselection()
        if not sel:
            return
        title = self.suggest_list.get(sel[0])
        self._select_in_listbox(title)
        # focus playlist so user can hit Enter to play or double-click
        self.playlist.focus_set()

    def _go_to_first_suggestion(self, _event):
        if self.suggest_list.size() > 0:
            title = self.suggest_list.get(0)
            self._select_in_listbox(title)
            self.play_selected()

    # ---------- Top Played (Max-Heap) ----------
    def show_top_played(self, top_k: int = 10):
        if not self.play_counts:
            messagebox.showinfo("Top Played", "No play history yet.")
            return
        heap = [(-cnt, title) for title, cnt in self.play_counts.items()]
        heapq.heapify(heap)
        items = []
        for _ in range(min(top_k, len(heap))):
            neg, title = heapq.heappop(heap)
            items.append((title, -neg))

        win = tk.Toplevel(self)
        win.title("Top Played")
        win.geometry("360x360")
        tree = ttk.Treeview(win, columns=("title", "count"), show="headings", height=14)
        tree.heading("title", text="Title")
        tree.heading("count", text="Plays")
        tree.column("title", width=240)
        tree.column("count", width=80, anchor="center")
        for title, cnt in items:
            tree.insert("", tk.END, values=(title, cnt))
        tree.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)

        def play_sel(_e=None):
            sel = tree.selection()
            if not sel:
                return
            title = tree.item(sel[0], "values")[0]
            node = self.node_by_title.get(title)
            if node:
                if self.current:
                    self.history_stack.append(self.current)
                self.play_node(node)

        ttk.Button(win, text="Play Selected", command=play_sel).pack(pady=(0, 8))
        tree.bind("<Double-Button-1>", play_sel)

    # ---------- Helpers ----------
    def _select_in_listbox(self, title: str):
        try:
            idxs = self.playlist.get(0, tk.END)
            for i, t in enumerate(idxs):
                if t == title:
                    self.playlist.selection_clear(0, tk.END)
                    self.playlist.selection_set(i)
                    self.playlist.see(i)
                    break
        except Exception:
            pass

    def _toggle_shuffle(self):
        self.shuffle_on = not self.shuffle_on
        self.shuffle_var.set(self.shuffle_on)
        self.status.config(text=f"Shuffle {'ON' if self.shuffle_on else 'OFF'}")

    def _poll_playback(self):
        """
        Tkinter-friendly polling loop:
        - If a song is playing and finishes (not paused), auto-advance.
        - Runs every 500ms.
        """
        try:
            if not self.engine.paused and self.current:
                if not self.engine.is_busy():
                    # Song finished → auto next
                    self.next_song()
        finally:
            self.after(500, self._poll_playback)


if __name__ == "__main__":
    app = MusicPlayerApp()
    app.mainloop()
