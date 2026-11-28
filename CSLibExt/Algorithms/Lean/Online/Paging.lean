/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.OfflineCaching
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Data.List.Nodup

/-!
# LRU paging is `k`-competitive

Online paging (Sleator and Tarjan, *Amortized efficiency of list update and paging rules*, 1985;
Borodin and El-Yaniv, *Online Computation and Competitive Analysis*, Chapter 3): a cache holds at
most `k` pages and each request for a page not in the cache is a miss. The least-recently-used
policy (`lruStep`: move the requested page to the front, keep the first `k`) is compared with
every legal trace of the cache system `cacheLTS` of `Greedy/OfflineCaching.lean`, in particular
with the optimal furthest-in-future manager there.

Main results:

* `lruTrace_spec`: LRU is a legal cache manager: its events (`lruEvent`, `lruTrace`) form a trace
  of `cacheLTS k`, serve exactly the requests, and miss exactly `lruMisses` times.
* `lruMisses_phase`: within a phase (a maximal block with at most `k` distinct pages,
  `phaseSplit`) LRU misses at most `k` times; the proof tracks the recency invariant
  (`lruStep_take_of_mem`, `lruStep_take_of_not_mem`): the most recent pages of the phase are
  exactly the front of the cache.
* The offline side uses the event API of `Greedy/OfflineCaching.lean` (`CacheEvent.request`,
  `CacheEvent.isMiss`, `misses`): a legal trace with capacity `h` misses at least `k + 1 - h`
  times on a segment that, together with a page already cached, requests `k + 1` distinct pages
  (`one_le_misses` there is the case `h = k`); so it misses that often between the second request
  of a phase and the first request of the next.
* `lruMisses_le` (**LRU is `k`-competitive**, Sleator and Tarjan): from any legal cache, LRU's
  trace misses at most `k * m + k` times on every request sequence, where `m` is the number of
  misses of any legal trace with the same capacity from any legal cache;
  `lruMisses_le_furthestInFuture`: the same against the offline optimum.
* `lruMisses_le_furthestInFuture_of_le` (**resource-augmented competitiveness of LRU**, Sleator
  and Tarjan, Theorem 6): for `1 ≤ h ≤ k`, the number `L` of misses of LRU with capacity `k`
  from any cache and the number `m` of misses of the offline optimum with capacity `h` from any
  legal cache satisfy `(k - h + 1) * L ≤ k * m + (k - h + 1) * h`.

## Cost model

The cost is the number of misses (`lruMisses`, `misses`), the standard measure of online paging;
there is no computation to charge.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Online.Paging

open Cslib.Algorithms.Lean.OfflineCaching

variable {α : Type*} [DecidableEq α]

/-! ## The LRU policy -/

/-- **One LRU step.** For a capacity $k$, a cache $c$ (a list of pages, most recently used first)
and a requested page $p$, the LRU step removes the first occurrence of $p$ from $c$ (if any), puts
$p$ at the front, and keeps the first $k$ pages of the result. On a miss with a cache of exactly
$k \ge 1$ pages, this evicts the last page, the least recently used one. -/
def lruStep (k : ℕ) (c : List α) (p : α) : List α := (p :: c.erase p).take k

/-- **Cache after LRU serves a request sequence.** For a capacity $k$, a cache $c$ (a list of
pages, most recently used first) and a request sequence $\sigma$, this is the cache obtained from
$c$ by applying one LRU step with capacity $k$ for each request of $\sigma$, in order. -/
def lruCache (k : ℕ) (c : List α) (σ : List α) : List α := σ.foldl (lruStep k) c

/-- **Number of LRU misses.** For a capacity $k$, a cache $c$ and a request sequence $\sigma$, this
is the number of requests of $\sigma$ that are not in the current cache when they are served,
where the cache starts at $c$ and after each request is updated by one LRU step with capacity
$k$. -/
def lruMisses (k : ℕ) : List α → List α → ℕ
  | _, [] => 0
  | c, p :: σ => (if p ∈ c then 0 else 1) + lruMisses k (lruStep k c p) σ

theorem lruMisses_append (k : ℕ) : ∀ (c σ τ : List α),
    lruMisses k c (σ ++ τ) = lruMisses k c σ + lruMisses k (lruCache k c σ) τ
  | c, [], τ => by simp [lruMisses, lruCache]
  | c, p :: σ, τ => by
      simp only [List.cons_append, lruMisses, lruCache, List.foldl_cons]
      rw [lruMisses_append k (lruStep k c p) σ τ]
      simp only [lruCache]
      omega

/-! ## List facts for the recency invariant -/

private theorem take_erase_of_mem {p : α} : ∀ {l : List α} {n : ℕ}, p ∈ l.take n →
    (l.erase p).take (n - 1) = (l.take n).erase p
  | [], _, h => by simp at h
  | a :: l, 0, h => by simp at h
  | a :: l, n + 1, h => by
      by_cases hap : a = p
      · subst hap; simp
      · have hp : p ∈ l.take n := by
          simp only [List.take_succ_cons, List.mem_cons] at h
          rcases h with h | h
          · exact absurd h.symm hap
          · exact h
        have hb : ¬((a == p) = true) := by simpa using hap
        rw [List.erase_cons_tail hb, List.take_succ_cons, List.erase_cons_tail hb]
        cases n with
        | zero => simp at hp
        | succ n =>
            simp only [Nat.add_sub_cancel, List.take_succ_cons]
            rw [← take_erase_of_mem hp]
            rfl

private theorem take_erase_of_not_mem {p : α} : ∀ {l : List α} {n : ℕ}, p ∉ l.take n →
    (l.erase p).take n = l.take n
  | [], _, _ => by simp
  | a :: l, 0, _ => by simp
  | a :: l, n + 1, h => by
      have hap : a ≠ p := fun hap => h (by simp [hap])
      have hp : p ∉ l.take n := fun hp => h (by simp [hp])
      have hb : ¬((a == p) = true) := by simpa using hap
      rw [List.erase_cons_tail hb, List.take_succ_cons, List.take_succ_cons,
        take_erase_of_not_mem hp]

/-- **The recency invariant for a repeated page.** Let $k$ be a capacity, $c$ a cache (most
recently used first) and $S$ a list of at most $k$ pages equal to the first $|S|$ pages of $c$.
If $p \in S$, then after one LRU step with capacity $k$ serving $p$, the first $|S|$ pages of the
cache are $p$ followed by $S$ with the first occurrence of $p$ removed. -/
theorem lruStep_take_of_mem {k : ℕ} {c S : List α} {p : α} (hS : c.take S.length = S)
    (hk : S.length ≤ k) (hp : p ∈ S) :
    (lruStep k c p).take S.length = p :: S.erase p := by
  have hpos : 0 < S.length := List.length_pos_of_mem hp
  obtain ⟨n, hn⟩ : ∃ n, S.length = n + 1 := ⟨S.length - 1, by omega⟩
  rw [lruStep, List.take_take, Nat.min_eq_left hk, hn, List.take_succ_cons]
  have hpc : p ∈ c.take S.length := by rw [hS]; exact hp
  have := take_erase_of_mem hpc
  rw [hn, Nat.add_sub_cancel] at this
  rw [this, ← hn, hS]

/-- **The recency invariant for a new page.** Let $k$ be a capacity, $c$ a cache (most recently
used first) and $S$ a list with $|S| + 1 \le k$ equal to the first $|S|$ pages of $c$. If
$p \notin S$, then after one LRU step with capacity $k$ serving $p$, the first $|S| + 1$ pages of
the cache are $p$ followed by $S$. -/
theorem lruStep_take_of_not_mem {k : ℕ} {c S : List α} {p : α} (hS : c.take S.length = S)
    (hk : S.length + 1 ≤ k) (hp : p ∉ S) :
    (lruStep k c p).take (S.length + 1) = p :: S := by
  rw [lruStep, List.take_take, Nat.min_eq_left hk, List.take_succ_cons]
  have hpc : p ∉ c.take S.length := by rw [hS]; exact hp
  rw [take_erase_of_not_mem hpc, hS]

/-! ## Phases -/

/-- **Splitting off a phase.** Given a capacity $k$ and a list $s$ of pages (the pages already in
the current phase, most recent first), a request sequence $\sigma$ is split into a phase and a
remainder as follows. The empty sequence splits into two empty parts. For a sequence $p$
followed by $\sigma'$: if $p$ is in $s$, then $p$ joins the phase and $\sigma'$ is split with $s$
replaced by $p$ followed by $s$ with its first occurrence of $p$ removed; if $p$ is not in $s$
and $s$ has fewer than $k$ entries, then $p$ joins the phase and $\sigma'$ is split with $p$
added at the front of $s$; otherwise the phase is empty and the remainder is the whole sequence.

When $s$ has no repetitions and at most $k$ pages, the phase is the longest prefix of $\sigma$
whose distinct pages, together with those of $s$, number at most $k$. -/
def phaseSplit (k : ℕ) : List α → List α → List α × List α
  | _, [] => ([], [])
  | seen, p :: rest =>
      if p ∈ seen then
        let r := phaseSplit k (p :: seen.erase p) rest
        (p :: r.1, r.2)
      else if seen.length < k then
        let r := phaseSplit k (p :: seen) rest
        (p :: r.1, r.2)
      else ([], p :: rest)

theorem phaseSplit_append (k : ℕ) : ∀ (seen σ : List α),
    (phaseSplit k seen σ).1 ++ (phaseSplit k seen σ).2 = σ
  | _, [] => rfl
  | seen, p :: rest => by
      simp only [phaseSplit]
      split_ifs
      · simp only [List.cons_append, phaseSplit_append k _ rest]
      · simp only [List.cons_append, phaseSplit_append k _ rest]
      · rfl

/-- **LRU misses at most $k - |S|$ times in the rest of a phase.** Let $k$ be a capacity, $c$ a
cache (most recently used first) and $S$ a duplicate-free list of at most $k$ pages equal to the
first $|S|$ pages of $c$. For every request sequence $\sigma$, let $\pi$ be the phase that the
phase split cuts from $\sigma$ with $S$ as the pages already in the phase: the longest prefix of
$\sigma$ whose distinct pages, together with those of $S$, number at most $k$. Then the number of
LRU misses with capacity $k$ serving $\pi$ from $c$, plus $|S|$, is at most $k$. -/
theorem lruMisses_phase (k : ℕ) : ∀ (seen c σ : List α), c.take seen.length = seen →
    seen.Nodup → seen.length ≤ k →
    lruMisses k c (phaseSplit k seen σ).1 + seen.length ≤ k
  | _, _, [], _, _, hk => by simpa [phaseSplit, lruMisses] using hk
  | seen, c, p :: rest, hS, hnd, hk => by
      simp only [phaseSplit]
      split_ifs with hp hlt
      · have hpc : p ∈ c := List.mem_of_mem_take (by rw [hS]; exact hp : p ∈ c.take seen.length)
        have hlen : (p :: seen.erase p).length = seen.length := by
          rw [List.length_cons, List.length_erase_of_mem hp]
          have := List.length_pos_of_mem hp
          omega
        have hS' : (lruStep k c p).take (p :: seen.erase p).length = p :: seen.erase p := by
          rw [hlen]; exact lruStep_take_of_mem hS hk hp
        have hnd' : (p :: seen.erase p).Nodup :=
          List.nodup_cons.2 ⟨fun h => (List.Nodup.mem_erase_iff hnd).1 h |>.1 rfl,
            hnd.erase p⟩
        have ih := lruMisses_phase k (p :: seen.erase p) (lruStep k c p) rest hS' hnd'
          (by rw [hlen]; exact hk)
        simp only [lruMisses, hpc, ↓reduceIte, Nat.zero_add]
        rw [hlen] at ih
        exact ih
      · have hS' : (lruStep k c p).take (p :: seen).length = p :: seen :=
          lruStep_take_of_not_mem hS hlt hp
        have ih := lruMisses_phase k (p :: seen) (lruStep k c p) rest hS'
          (List.nodup_cons.2 ⟨hp, hnd⟩) hlt
        simp only [lruMisses, List.length_cons] at ih ⊢
        split_ifs <;> omega
      · simp only [lruMisses]; omega

theorem phaseSplit_ne_nil {k : ℕ} (hk : 1 ≤ k) {σ : List α} (hσ : σ ≠ []) :
    (phaseSplit k [] σ).1 ≠ [] := by
  obtain ⟨p, rest, rfl⟩ := List.exists_cons_of_ne_nil hσ
  simp only [phaseSplit, List.not_mem_nil, ↓reduceIte, List.length_nil,
    show 0 < k by omega, ne_eq, reduceCtorEq, not_false_eq_true]

/-- **A phase ends only on a $(k + 1)$-st distinct page.** Let $k$ be a capacity, let $s$ be a
list of pages without repetitions with at most $k$ pages (the pages already in the current
phase), and let $\sigma$ be a request sequence. If the remainder left after splitting off a phase
from $\sigma$ given $s$ starts with a page $q$, then there is a list $S$ of exactly $k$ pairwise
distinct pages, none equal to $q$, each of which lies in $s$ or in that phase. -/
theorem phaseSplit_snd_cons (k : ℕ) : ∀ (seen σ : List α) (q : α) (rest : List α),
    seen.Nodup → seen.length ≤ k → (phaseSplit k seen σ).2 = q :: rest →
    ∃ S : List α, S.Nodup ∧ S.length = k ∧ q ∉ S ∧
      ∀ x ∈ S, x ∈ seen ∨ x ∈ (phaseSplit k seen σ).1
  | _, [], _, _, _, _, h => by simp [phaseSplit] at h
  | seen, p :: σ, q, rest, hnd, hk, h => by
      simp only [phaseSplit] at h ⊢
      split_ifs at h ⊢ with hp hlt
      · have hlen : (p :: seen.erase p).length = seen.length := by
          rw [List.length_cons, List.length_erase_of_mem hp]
          have := List.length_pos_of_mem hp
          omega
        have hnd' : (p :: seen.erase p).Nodup :=
          List.nodup_cons.2 ⟨fun h => (List.Nodup.mem_erase_iff hnd).1 h |>.1 rfl,
            hnd.erase p⟩
        obtain ⟨S, hS, hSl, hq, hsub⟩ :=
          phaseSplit_snd_cons k _ σ q rest hnd' (by rw [hlen]; exact hk) h
        refine ⟨S, hS, hSl, hq, fun x hx => ?_⟩
        rcases hsub x hx with h1 | h1
        · rcases List.mem_cons.1 h1 with rfl | h1
          · exact Or.inl hp
          · exact Or.inl (List.mem_of_mem_erase h1)
        · exact Or.inr (List.mem_cons_of_mem _ h1)
      · obtain ⟨S, hS, hSl, hq, hsub⟩ :=
          phaseSplit_snd_cons k _ σ q rest (List.nodup_cons.2 ⟨hp, hnd⟩) hlt h
        refine ⟨S, hS, hSl, hq, fun x hx => ?_⟩
        rcases hsub x hx with h1 | h1
        · rcases List.mem_cons.1 h1 with rfl | h1
          · exact Or.inr List.mem_cons_self
          · exact Or.inl h1
        · exact Or.inr (List.mem_cons_of_mem _ h1)
      · obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact ⟨seen, hnd, by omega, hp, fun x hx => Or.inl hx⟩

/-! ## LRU as a legal cache manager -/

/-- **The event of an LRU step.** For a capacity $k$, a cache $c$ (a list of pages, most recently
used first) and a requested page $p$, the LRU event is a hit on $p$ if $p \in c$. Otherwise it is
a miss on $p$ that evicts the last page of $c$ (the least recently used one) if $c$ is nonempty,
$k > 0$ and $c$ has at least $k$ pages, and a miss on $p$ without eviction in all other cases. -/
def lruEvent (k : ℕ) (c : List α) (p : α) : CacheEvent α :=
  if p ∈ c then .hit p
  else if h : c ≠ [] ∧ k ≤ c.length ∧ 0 < k then .miss p (some (c.getLast h.1))
  else .miss p none

/-- **The LRU trace.** Given a capacity $k$, a cache $c$ and a request sequence $\sigma$, the
events LRU emits on $\sigma$ from $c$: nothing on the empty sequence, and on a sequence $p$
followed by $\sigma'$, the event LRU emits when serving $p$ from $c$, followed by the events LRU
emits on $\sigma'$ from the cache after one LRU step with capacity $k$ serving $p$ from $c$. -/
def lruTrace (k : ℕ) : List α → List α → List (CacheEvent α)
  | _, [] => []
  | c, p :: σ => lruEvent k c p :: lruTrace k (lruStep k c p) σ

theorem lruStep_valid {k : ℕ} {c : List α} (p : α) (hnd : c.Nodup) :
    (lruStep k c p).Nodup ∧ (lruStep k c p).length ≤ k :=
  ⟨(List.nodup_cons.2 ⟨fun h => (List.Nodup.mem_erase_iff hnd).1 h |>.1 rfl,
      hnd.erase p⟩).sublist (List.take_sublist _ _), List.length_take_le _ _⟩

private theorem erase_getLast {c : List α} (hnd : c.Nodup) (h : c ≠ []) :
    c.erase (c.getLast h) = c.dropLast := by
  generalize ha : c.getLast h = a
  have hc : c = c.dropLast ++ [a] := by rw [← ha, List.dropLast_append_getLast]
  generalize c.dropLast = l at hc ⊢
  subst hc
  have hal : a ∉ l := fun hm => (List.nodup_append.1 hnd).2.2 _ hm _ (List.mem_singleton_self a) rfl
  rw [List.erase_append_right _ hal, List.erase_cons_head, List.append_nil]

/-- **Each LRU step is a legal transition.** Let $k$ be a capacity and $c$ a duplicate-free cache
with at most $k$ pages. For every page $p$, the cache system with capacity $k$ has a transition
from $c$, labelled by the LRU event for $p$ at $c$, to the cache produced by one LRU step with
capacity $k$ serving $p$. -/
theorem lru_tr {k : ℕ} {c : List α} (p : α) (hnd : c.Nodup) (hck : c.length ≤ k) :
    (cacheLTS k).Tr c (lruEvent k c p) (lruStep k c p) := by
  unfold lruEvent lruStep
  by_cases hp : p ∈ c
  · simp only [hp, ↓reduceIte]
    have hlen : (p :: c.erase p).length ≤ k := by
      rw [List.length_cons, List.length_erase_of_mem hp]
      have := List.length_pos_of_mem hp
      omega
    rw [List.take_of_length_le hlen]
    exact ⟨hp, (List.perm_cons_erase hp).symm⟩
  · simp only [hp, ↓reduceIte, List.erase_of_not_mem hp]
    split
    · next hfull =>
      have hk : c.length = k := by omega
      refine ⟨hfull.2.2, hp, hk, List.getLast_mem _, ?_⟩
      rw [erase_getLast hnd hfull.1, List.dropLast_eq_take, hk]
      obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [hj, List.take_succ_cons, Nat.add_sub_cancel]
    · next hfull =>
      refine ⟨hp, ?_⟩
      by_cases hk0 : k = 0
      · subst hk0
        left
        exact ⟨rfl, List.eq_nil_of_length_eq_zero (by omega), rfl⟩
      · right
        have hlt : c.length < k := by
          by_cases hc : c = []
          · subst hc; simp only [List.length_nil]; omega
          · have : ¬ k ≤ c.length := fun h' => hfull ⟨hc, h', by omega⟩
            omega
        refine ⟨hlt, ?_⟩
        rw [List.take_of_length_le (by simp only [List.length_cons]; omega)]

/-- **LRU is a legal cache manager.** Let $k$ be a capacity, $c$ a cache given as a list of pages
without repetitions with at most $k$ pages, and $\sigma$ a request sequence. Then the sequence of
events that LRU emits when serving $\sigma$ from $c$ is a run of the cache system with capacity
$k$ from $c$ to the cache LRU holds after serving $\sigma$; the pages requested by these events are
exactly $\sigma$, in order; and the number of misses among these events equals the number of
misses of LRU on $\sigma$ from $c$. -/
theorem lruTrace_spec {k : ℕ} : ∀ (c σ : List α), c.Nodup → c.length ≤ k →
    (cacheLTS k).MTr c (lruTrace k c σ) (lruCache k c σ) ∧
      (lruTrace k c σ).map CacheEvent.request = σ ∧
      misses (lruTrace k c σ) = lruMisses k c σ
  | c, [], _, _ => ⟨Cslib.LTS.MTr.refl, rfl, rfl⟩
  | c, p :: σ, hnd, hck => by
      obtain ⟨h1, h2⟩ := lruStep_valid (k := k) p hnd
      obtain ⟨ih1, ih2, ih3⟩ := lruTrace_spec (lruStep k c p) σ h1 h2
      refine ⟨Cslib.LTS.MTr.stepL (lru_tr p hnd hck) ih1, ?_, ?_⟩
      · simp only [lruTrace, List.map_cons, ih2]
        congr 1
        unfold lruEvent
        split_ifs <;> rfl
      · simp only [lruTrace, misses, lruMisses] at ih3 ⊢
        rw [List.countP_cons, ih3]
        by_cases hp : p ∈ c
        · have he : lruEvent k c p = .hit p := by simp only [lruEvent, hp, ↓reduceIte]
          simp only [he, CacheEvent.isMiss, hp, ↓reduceIte, Bool.false_eq_true]
          omega
        · have he : CacheEvent.isMiss (lruEvent k c p) = true := by
            unfold lruEvent
            simp only [hp, ↓reduceIte]
            split <;> rfl
          simp only [he, hp, ↓reduceIte]
          omega

/-! ## LRU is `k`-competitive -/

/-- In the rest of a phase, LRU misses at most once on each page that is not yet in the phase:
the pages already in the phase are at the front of the cache. -/
private theorem exists_lruMisses_phase_le (k : ℕ) : ∀ (seen c σ : List α),
    c.take seen.length = seen → seen.Nodup → seen.length ≤ k →
    ∃ D : List α, D.Nodup ∧ (∀ x ∈ D, x ∉ seen ∧ x ∈ σ) ∧
      lruMisses k c (phaseSplit k seen σ).1 ≤ D.length
  | _, _, [], _, _, _ => ⟨[], List.nodup_nil, by simp, by simp [phaseSplit, lruMisses]⟩
  | seen, c, p :: rest, hS, hnd, hk => by
      simp only [phaseSplit]
      split_ifs with hp hlt
      · have hpc : p ∈ c := List.mem_of_mem_take (by rw [hS]; exact hp : p ∈ c.take seen.length)
        have hlen : (p :: seen.erase p).length = seen.length := by
          rw [List.length_cons, List.length_erase_of_mem hp]
          have := List.length_pos_of_mem hp
          omega
        have hS' : (lruStep k c p).take (p :: seen.erase p).length = p :: seen.erase p := by
          rw [hlen]; exact lruStep_take_of_mem hS hk hp
        have hnd' : (p :: seen.erase p).Nodup :=
          List.nodup_cons.2 ⟨fun h => (List.Nodup.mem_erase_iff hnd).1 h |>.1 rfl,
            hnd.erase p⟩
        obtain ⟨D, hD, hsub, hle⟩ := exists_lruMisses_phase_le k (p :: seen.erase p)
          (lruStep k c p) rest hS' hnd' (by rw [hlen]; exact hk)
        refine ⟨D, hD, fun x hx => ⟨fun hxs => ?_, List.mem_cons_of_mem _ (hsub x hx).2⟩, ?_⟩
        · by_cases hxp : x = p
          · exact (hsub x hx).1 (hxp ▸ List.mem_cons_self)
          · exact (hsub x hx).1
              (List.mem_cons_of_mem _ ((List.Nodup.mem_erase_iff hnd).2 ⟨hxp, hxs⟩))
        · simpa only [lruMisses, hpc, ↓reduceIte, Nat.zero_add] using hle
      · have hS' : (lruStep k c p).take (p :: seen).length = p :: seen :=
          lruStep_take_of_not_mem hS hlt hp
        obtain ⟨D, hD, hsub, hle⟩ := exists_lruMisses_phase_le k (p :: seen) (lruStep k c p) rest
          hS' (List.nodup_cons.2 ⟨hp, hnd⟩) hlt
        refine ⟨p :: D, List.nodup_cons.2 ⟨fun h => (hsub p h).1 List.mem_cons_self, hD⟩,
          fun x hx => ?_, ?_⟩
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact ⟨hp, List.mem_cons_self⟩
          · exact ⟨fun h => (hsub x hx).1 (List.mem_cons_of_mem _ h),
              List.mem_cons_of_mem _ (hsub x hx).2⟩
        · simp only [lruMisses, List.length_cons]
          split_ifs <;> omega
      · exact ⟨[], List.nodup_nil, by simp, by simp [lruMisses]⟩

/-- A cache transition adds at most the page it serves. -/
private theorem eq_request_or_mem_of_tr {capacity : ℕ} {before after : List α}
    {e : CacheEvent α} (h : (cacheLTS capacity).Tr before e after) {x : α} (hx : x ∈ after) :
    x = e.request ∨ x ∈ before := by
  cases e with
  | hit r => exact Or.inr (h.2.mem_iff.1 hx)
  | miss r v =>
      cases v with
      | none =>
          obtain ⟨_, (⟨_, _, rfl⟩ | ⟨_, hperm⟩)⟩ := h
          · simp at hx
          · simpa using hperm.mem_iff.1 hx
      | some v =>
          obtain ⟨_, _, _, _, hperm⟩ := h
          rcases List.mem_cons.1 (hperm.mem_iff.1 hx) with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_of_mem_erase h)

/-- A legal trace misses at least once on each page it serves that its initial cache lacks. -/
private theorem length_le_misses {capacity : ℕ} {before after : List α}
    {events : List (CacheEvent α)} (h : (cacheLTS capacity).MTr before events after) :
    ∀ {distinct : List α}, distinct.Nodup →
      (∀ x ∈ distinct, x ∉ before ∧ x ∈ events.map CacheEvent.request) →
      distinct.length ≤ misses events := by
  induction h with
  | refl =>
      intro distinct _ hsub
      cases distinct with
      | nil => exact Nat.zero_le _
      | cons x _ => simpa using (hsub x List.mem_cons_self).2
  | @stepL s1 e s2 es s3 htr _ ih =>
      intro distinct hd hsub
      have hnew : ∀ x, x ≠ e.request → x ∉ s1 → x ∉ s2 := fun x hxr hx1 hx2 =>
        (eq_request_or_mem_of_tr htr hx2).elim hxr hx1
      cases e with
      | hit r =>
          have hr : r ∈ s1 := htr.1
          have := ih hd fun x hx => by
            obtain ⟨hx1, hx2⟩ := hsub x hx
            have hxr : x ≠ r := fun h => hx1 (h ▸ hr)
            exact ⟨hnew x hxr hx1, by simpa [hxr] using hx2⟩
          simpa [misses] using this
      | miss r v =>
          have := ih (hd.erase r) fun x hx => by
            obtain ⟨hxr, hx⟩ := (List.Nodup.mem_erase_iff hd).1 hx
            obtain ⟨hx1, hx2⟩ := hsub x hx
            exact ⟨hnew x hxr hx1, by simpa [hxr] using hx2⟩
          have hlen : distinct.length ≤ (distinct.erase r).length + 1 := by
            by_cases hr : r ∈ distinct
            · rw [List.length_erase_of_mem hr]; omega
            · rw [List.erase_of_not_mem hr]; omega
          have hm : misses (CacheEvent.miss r v :: es) = misses es + 1 :=
            List.countP_cons_of_pos rfl
          omega

/-- A legal trace misses at least `|D| - |C|` times if each page of a duplicate-free list `D` lies
in its initial cache `C` or is served by the trace. -/
private theorem length_le_length_add_misses {capacity : ℕ} {before after : List α}
    {events : List (CacheEvent α)} (h : (cacheLTS capacity).MTr before events after)
    {distinct : List α} (hd : distinct.Nodup)
    (hsub : ∀ x ∈ distinct, x ∈ before ∨ x ∈ events.map CacheEvent.request) :
    distinct.length ≤ before.length + misses events := by
  have hsplit := List.length_eq_length_filter_add (l := distinct) fun x => decide (x ∈ before)
  have h1 : (distinct.filter fun x => decide (x ∈ before)).length ≤ before.length :=
    ((hd.filter _).subperm fun x hx => by simpa using (List.mem_filter.1 hx).2).length_le
  have h2 := length_le_misses h (distinct := distinct.filter fun x => !decide (x ∈ before))
    (hd.filter _) fun x hx => by
      obtain ⟨hx, hxb⟩ := List.mem_filter.1 hx
      have hxb : x ∉ before := by simpa using hxb
      exact ⟨hxb, (hsub x hx).resolve_left hxb⟩
  omega

omit [DecidableEq α] in
private theorem misses_tail_le (es : List (CacheEvent α)) : misses es.tail ≤ misses es := by
  cases es with
  | nil => exact le_refl _
  | cons e es =>
      simp only [List.tail_cons, misses, List.countP_cons]
      omega

/-- The phase argument, by induction on the phases, for an offline cache of `h ≤ k` pages. LRU
misses at most `k` times per phase, while a legal trace with capacity `h` misses at least
`k - h + 1` times between the second request of a phase and the first request of the next. In
the last phase, LRU misses at most once on its first request and once on each other page of the
phase, while the trace misses on all but `h - 1` of those other pages. -/
private theorem lruMisses_le_tail {k h : ℕ} (hh : 1 ≤ h) (hhk : h ≤ k) :
    ∀ (n : ℕ) (σ : List α), σ.length ≤ n →
    ∀ (c c0 cf : List α) (es : List (CacheEvent α)), (cacheLTS h).MTr c0 es cf → c0.Nodup →
    c0.length ≤ h → es.map CacheEvent.request = σ → σ ≠ [] →
    (k - h + 1) * lruMisses k c σ ≤ k * misses es.tail + (k - h + 1) * h
  | 0, σ, hn, _, _, _, _, _, _, _, _, hσ => by
      exact absurd (List.eq_nil_of_length_eq_zero (by omega)) hσ
  | n + 1, σ, hn, c, c0, cf, es, hes, hnd, hck, hmap, hσ => by
      have hk : 1 ≤ k := le_trans hh hhk
      obtain ⟨p, rest, rfl⟩ := List.exists_cons_of_ne_nil hσ
      obtain ⟨e0, es', rfl⟩ : ∃ e0 es', es = e0 :: es' := by
        cases es with
        | nil => exact absurd hmap (by simp)
        | cons e0 es' => exact ⟨e0, es', rfl⟩
      -- the first event leads from `c0` to a cache `c1` holding the first request `p`
      obtain ⟨c1, hc1, h1⟩ := Cslib.LTS.MTr.cons_iff.1 hes
      obtain ⟨hv1, hv2⟩ := cacheLTS_valid hc1 hnd hck
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hreq, hmap⟩ := hmap
      have hp : p ∈ c1 := hreq ▸ request_mem_of_tr (by omega) hc1
      simp only [List.tail_cons]
      -- the first phase is `p` followed by `P`, and `R` is the rest
      set P := (phaseSplit k [p] rest).1 with hP
      set R := (phaseSplit k [p] rest).2 with hR
      have hsplit : phaseSplit k [] (p :: rest) = (p :: P, R) := by
        simp [phaseSplit, show 0 < k by omega, hP, hR]
      have hPR : P ++ R = rest := phaseSplit_append k [p] rest
      have hphase : lruMisses k c (p :: P) ≤ k := by
        simpa [hsplit] using
          lruMisses_phase k [] c (p :: rest) (by simp) List.nodup_nil (Nat.zero_le _)
      cases hRc : R with
      | nil =>
          -- the last phase
          rw [hRc, List.append_nil] at hPR
          have htake : (lruStep k c p).take [p].length = [p] := by
            obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
            simp [lruStep]
          obtain ⟨D, hD, hDsub, hDle⟩ := exists_lruMisses_phase_le k [p] (lruStep k c p) rest
            htake (List.nodup_singleton p) (by simpa using hk)
          rw [← hP, hPR] at hDle
          rw [hPR] at hphase
          have hL : lruMisses k c (p :: rest) ≤ D.length + 1 := by
            simp only [lruMisses]; split_ifs <;> omega
          have hM : D.length + 1 ≤ h + misses es' := by
            have := length_le_length_add_misses h1 (distinct := p :: D)
              (List.nodup_cons.2 ⟨fun hpD => (hDsub p hpD).1 List.mem_cons_self, hD⟩)
              fun x hx => by
                rcases List.mem_cons.1 hx with rfl | hx
                · exact Or.inl hp
                · exact Or.inr (hmap ▸ (hDsub x hx).2)
            simp only [List.length_cons] at this
            omega
          generalize lruMisses k c (p :: rest) = L at hL hphase ⊢
          by_cases hLh : L ≤ h
          · exact (Nat.mul_le_mul_left _ hLh).trans (Nat.le_add_left _ _)
          · obtain ⟨t, rfl⟩ : ∃ t, L = h + t := ⟨L - h, by omega⟩
            have : (k - h + 1) * t ≤ k * misses es' := Nat.mul_le_mul (by omega) (by omega)
            rw [Nat.mul_add]
            omega
      | cons q R' =>
          rw [hRc] at hPR
          obtain ⟨S, hS, hSl, hqS, hSsub⟩ :=
            phaseSplit_snd_cons k [] (p :: rest) q R' List.nodup_nil (Nat.zero_le _)
              (by rw [hsplit]; exact hRc)
          rw [hsplit] at hSsub
          simp only [List.not_mem_nil, false_or] at hSsub
          -- split the rest of the trace at the end of the phase
          have hsplit' : es' = es'.take P.length ++ es'.drop P.length :=
            (List.take_append_drop _ _).symm
          obtain ⟨cm, h2, h3⟩ := Cslib.LTS.MTr.split (hsplit' ▸ h1)
          have hmap1 : (es'.take P.length).map CacheEvent.request = P := by
            rw [List.map_take, hmap, ← hPR, List.take_left]
          have hmap2 : (es'.drop P.length).map CacheEvent.request = q :: R' := by
            rw [List.map_drop, hmap, ← hPR, List.drop_left]
          obtain ⟨e2, es2, hes2⟩ : ∃ e2 es2, es'.drop P.length = e2 :: es2 := by
            cases hd : es'.drop P.length with
            | nil => rw [hd, List.map_nil] at hmap2; exact absurd hmap2 (List.cons_ne_nil _ _).symm
            | cons e2 es2 => exact ⟨e2, es2, rfl⟩
          rw [hes2] at h3 hmap2
          obtain ⟨hcm1, hcm2⟩ := cacheLTS_mtr_valid h2 hv1 hv2
          have ih := lruMisses_le_tail hh hhk n (q :: R') (by
              have := congrArg List.length hPR
              simp only [List.length_append, List.length_cons] at this hn ⊢
              omega) (lruCache k c (p :: P)) cm cf (e2 :: es2) h3 hcm1 hcm2 hmap2
              (List.cons_ne_nil _ _)
          simp only [List.tail_cons] at ih
          -- the segment from the second request of the phase to the first request of the next
          obtain ⟨c2, hc2, -⟩ := Cslib.LTS.MTr.cons_iff.1 h3
          have hseg : (cacheLTS h).MTr c1 (es'.take P.length ++ [e2]) c2 :=
            Cslib.LTS.MTr.comp (cacheLTS h) h2 (Cslib.LTS.MTr.single (cacheLTS h) hc2)
          simp only [List.map_cons, List.cons.injEq] at hmap2
          have hsegm : k + 1 ≤ h + misses (es'.take P.length ++ [e2]) := by
            have := length_le_length_add_misses hseg (distinct := q :: S)
              (List.nodup_cons.2 ⟨hqS, hS⟩) fun x hx => by
                rcases List.mem_cons.1 hx with rfl | hx
                · right; simp [hmap2.1]
                · rcases List.mem_cons.1 (hSsub x hx) with rfl | hxP
                  · exact Or.inl hp
                  · right
                    simp only [List.map_append, List.map_cons, List.map_nil, hmap1]
                    exact List.mem_append_left _ hxP
            simp only [List.length_cons, hSl] at this
            omega
          have hmt : misses es' = misses (es'.take P.length ++ [e2]) + misses es2 := by
            conv_lhs => rw [hsplit', hes2]
            rw [← misses_append, List.append_assoc, List.singleton_append]
          have hseg' : (k - h + 1) * lruMisses k c (p :: P) ≤
              k * misses (es'.take P.length ++ [e2]) :=
            calc (k - h + 1) * lruMisses k c (p :: P) ≤ (k - h + 1) * k :=
                  Nat.mul_le_mul_left _ hphase
              _ = k * (k - h + 1) := Nat.mul_comm _ _
              _ ≤ k * misses (es'.take P.length ++ [e2]) := Nat.mul_le_mul_left _ (by omega)
          rw [show p :: rest = (p :: P) ++ q :: R' by rw [← hPR]; rfl, lruMisses_append, hmt]
          simp only [Nat.mul_add]
          omega

/-- The competitive bound for an arbitrary starting list `c` (used by `lruMisses_le`, which
restricts `c` to a legal cache). -/
private theorem lruMisses_le_of_list {k : ℕ} (hk : 1 ≤ k) (c : List α) {c0 cf : List α}
    {es : List (CacheEvent α)} (hes : (cacheLTS k).MTr c0 es cf) (hnd : c0.Nodup)
    (hck : c0.length ≤ k) : lruMisses k c (es.map CacheEvent.request) ≤ k * misses es + k := by
  by_cases hσ : es.map CacheEvent.request = []
  · rw [hσ]; simp [lruMisses]
  · have h := lruMisses_le_tail hk le_rfl _ (es.map CacheEvent.request) (le_refl _) c c0 cf es
      hes hnd hck rfl hσ
    simp only [Nat.sub_self, Nat.zero_add, Nat.one_mul] at h
    have := Nat.mul_le_mul_left k (misses_tail_le es)
    omega

/-- **LRU is $k$-competitive.** Let $k \ge 1$ and let $c$ be a duplicate-free cache with at most
$k$ pages. Let $e$ be a legal trace of the cache system with capacity $k$ that starts from a
duplicate-free cache with at most $k$ pages, and let $m$ be its number of misses. Then the trace
that LRU with capacity $k$ emits when serving, from $c$, the requests of $e$ in order has at most
$k m + k$ misses.

This is the bound of Sleator and Tarjan for an online and an offline cache of the same size. -/
theorem lruMisses_le {k : ℕ} (hk : 1 ≤ k) {c : List α} (hc : c.Nodup) (hcl : c.length ≤ k)
    {c0 cf : List α} {es : List (CacheEvent α)} (hes : (cacheLTS k).MTr c0 es cf)
    (hnd : c0.Nodup) (hck : c0.length ≤ k) :
    misses (lruTrace k c (es.map CacheEvent.request)) ≤ k * misses es + k := by
  rw [(lruTrace_spec c _ hc hcl).2.2]
  exact lruMisses_le_of_list hk c hes hnd hck

/-- **LRU is $k$-competitive against the offline optimum.** Let $k \ge 1$, and let $c$ and $c_0$
be duplicate-free caches with at most $k$ pages each. For every request sequence $\sigma$, the
trace that LRU with capacity $k$ emits when serving $\sigma$ from $c$ has at most $k m + k$
misses, where $m$ is the number of misses of the furthest-in-future manager with capacity $k$
serving $\sigma$ from $c_0$.

Furthest-in-future misses no more often than any legal trace serving the same requests from the
same cache, so it is the offline optimum. -/
theorem lruMisses_le_furthestInFuture {k : ℕ} (hk : 1 ≤ k) {c : List α} (hc : c.Nodup)
    (hcl : c.length ≤ k) (requests : List α) {c0 : List α} (hnd : c0.Nodup)
    (hck : c0.length ≤ k) :
    misses (lruTrace k c requests) ≤ k * misses (furthestInFuture k requests c0).1 + k := by
  obtain ⟨hlegal, -, -⟩ := furthestInFuture_legal k requests c0 hnd hck
  have := lruMisses_le hk hc hcl hlegal hnd hck
  rwa [furthestInFuture_requests k requests c0 hnd hck] at this

/-! ## Resource augmentation -/

/-- **Resource-augmented competitiveness of LRU** (Sleator and Tarjan, *Amortized efficiency of
list update and paging rules*, Communications of the ACM 28(2), 1985, Section 4, Theorem 6). Let
$1 \le h \le k$, let $c$ be any list of pages (the initial cache of LRU, most recently used
first), and let $c_0$ be a duplicate-free cache with at most $h$ pages. For every request sequence
$\sigma$, let $L$ be the number of misses of LRU with capacity $k$ serving $\sigma$ from $c$, and
let $m$ be the number of misses of the furthest-in-future manager (the offline optimum) with
capacity $h$ serving $\sigma$ from $c_0$. Then $(k - h + 1) L \le k m + (k - h + 1) h$, that is,
$L \le \frac{k}{k - h + 1} m + h$. -/
theorem lruMisses_le_furthestInFuture_of_le {k h : ℕ} (hh : 1 ≤ h) (hhk : h ≤ k)
    (c requests : List α) {c0 : List α} (hnd : c0.Nodup) (hck : c0.length ≤ h) :
    (k - h + 1) * lruMisses k c requests ≤
      k * misses (furthestInFuture h requests c0).1 + (k - h + 1) * h := by
  by_cases hσ : requests = []
  · subst hσ; simp [lruMisses]
  · obtain ⟨hlegal, -, -⟩ := furthestInFuture_legal h requests c0 hnd hck
    have := lruMisses_le_tail hh hhk _ requests le_rfl c c0 _ _ hlegal hnd hck
      (furthestInFuture_requests h requests c0 hnd hck) hσ
    have := Nat.mul_le_mul_left k (misses_tail_le (furthestInFuture h requests c0).1)
    omega

end Cslib.Algorithms.Lean.Online.Paging
