/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Online.PagingLowerBound

/-!
# FIFO paging is `k`-competitive

First-in first-out paging (Sleator and Tarjan, *Amortized efficiency of list update and paging
rules*, CACM 1985; Borodin and El-Yaniv, *Online Computation and Competitive Analysis*,
Chapter 3): on a miss with a full cache, evict the page that was loaded earliest (`fifoStep`;
the cache is a queue, oldest first). Like LRU (`Paging.lean`), FIFO is `k`-competitive.

Main results:

* `policyMisses_le`: the phase argument of `Paging.lean` for any policy on list caches that
  misses at most `k` times per phase (`phaseSplit`); `policyMisses_lruStep`: LRU is such a policy
  (`lruMisses` is its `policyMisses`).
* `fifoMisses_phase`: **FIFO misses at most `k` times per phase**: the pages loaded in the phase
  stay at the back of the queue, so each is missed at most once.
* `fifoStep_legal`, `fifoCache_legal`: FIFO keeps a legal cache (`LegalCache`); `fifoPager` is
  FIFO as an `OnlinePager` (`PagingLowerBound.lean`), with `fifoPager_misses` bridging the counts.
* `fifoMisses_le` (**FIFO is `k`-competitive**): from a legal cache, FIFO misses at most
  `k * m + k` times, where `m` counts the misses of any legal trace with the same capacity;
  `fifoMisses_le_furthestInFuture`: the same against the offline optimum;
  `fifo_not_competitive_of_lt`: the ratio `k` is tight (`not_competitive_of_lt`).

## Cost model

The cost is the number of misses (`policyMisses`); there is no computation to charge.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Online.FifoPaging

open Cslib.Algorithms.Lean.OfflineCaching Cslib.Algorithms.Lean.Online.Paging

variable {α : Type*} [DecidableEq α]

/-! ## Policies on list caches -/

/-- The misses of a paging policy given by its step on list caches. -/
def policyMisses (step : List α → α → List α) : List α → List α → ℕ
  | _, [] => 0
  | c, p :: σ => (if p ∈ c then 0 else 1) + policyMisses step (step c p) σ

theorem policyMisses_append (step : List α → α → List α) : ∀ (c σ τ : List α),
    policyMisses step c (σ ++ τ) = policyMisses step c σ + policyMisses step (σ.foldl step c) τ
  | _, [], _ => by simp [policyMisses]
  | c, p :: σ, τ => by
      simp only [List.cons_append, policyMisses, List.foldl_cons,
        policyMisses_append step (step c p) σ τ]
      omega

/-- The phase argument for any policy that misses at most `k` times per phase (the argument of
`Paging.lean` for LRU, with the phase bound as a hypothesis). -/
private theorem policyMisses_le_tail (step : List α → α → List α) {k : ℕ} (hk : 1 ≤ k)
    (hphase : ∀ c σ : List α, policyMisses step c (phaseSplit k [] σ).1 ≤ k) :
    ∀ (n : ℕ) (σ : List α), σ.length ≤ n →
    ∀ (c c0 cf : List α) (es : List (CacheEvent α)), (cacheLTS k).MTr c0 es cf → c0.Nodup →
    c0.length ≤ k → es.map CacheEvent.request = σ → σ ≠ [] →
    policyMisses step c σ ≤ k * misses es.tail + k
  | 0, σ, hn, _, _, _, _, _, _, _, _, hσ => by
      exact absurd (List.eq_nil_of_length_eq_zero (by omega)) hσ
  | n + 1, σ, hn, c, c0, cf, es, hes, hnd, hck, hmap, hσ => by
      set P := (phaseSplit k [] σ).1 with hP
      set R := (phaseSplit k [] σ).2 with hR
      have hσPR : P ++ R = σ := phaseSplit_append k [] σ
      have hPne : P ≠ [] := phaseSplit_ne_nil hk hσ
      have hph : policyMisses step c P ≤ k := hphase c σ
      rw [← hσPR, policyMisses_append]
      cases hRc : R with
      | nil => simp only [policyMisses]; omega
      | cons q R' =>
          obtain ⟨S, hS, hSl, hqS, hSsub⟩ :=
            phaseSplit_snd_cons k [] σ q R' List.nodup_nil (Nat.zero_le _) (hR.symm.trans hRc)
          simp only [List.not_mem_nil, false_or] at hSsub
          have hsplit : es = es.take P.length ++ es.drop P.length :=
            (List.take_append_drop _ _).symm
          obtain ⟨cm, h1, h2⟩ := Cslib.LTS.MTr.split (hsplit ▸ hes)
          have hmap1 : (es.take P.length).map CacheEvent.request = P := by
            rw [List.map_take, hmap, ← hσPR, List.take_left]
          have hmap2 : (es.drop P.length).map CacheEvent.request = q :: R' := by
            rw [List.map_drop, hmap, ← hσPR, List.drop_left, hRc]
          obtain ⟨hcm1, hcm2⟩ := cacheLTS_mtr_valid h1 hnd hck
          have ih := policyMisses_le_tail step hk hphase n (q :: R') (by
              have := congrArg List.length hσPR
              rw [List.length_append, hRc] at this
              have : 1 ≤ P.length := List.length_pos_iff.2 hPne
              omega) (P.foldl step c) cm cf (es.drop P.length) h2 hcm1 hcm2 hmap2
              (List.cons_ne_nil _ _)
          obtain ⟨e0, es1, hes1⟩ : ∃ e0 es1, es.take P.length = e0 :: es1 := by
            cases h : es.take P.length with
            | nil => rw [h, List.map_nil] at hmap1; exact absurd hmap1.symm hPne
            | cons e0 es1 => exact ⟨e0, es1, rfl⟩
          obtain ⟨e2, es2, hes2⟩ : ∃ e2 es2, es.drop P.length = e2 :: es2 := by
            cases h : es.drop P.length with
            | nil => rw [h, List.map_nil] at hmap2; exact absurd hmap2 (List.cons_ne_nil _ _).symm
            | cons e2 es2 => exact ⟨e2, es2, rfl⟩
          rw [hes1] at h1 hmap1
          rw [hes2] at h2 hmap2 ih
          obtain ⟨c1, hc1, h1'⟩ := Cslib.LTS.MTr.cons_iff.1 h1
          obtain ⟨c2, hc2, h2'⟩ := Cslib.LTS.MTr.cons_iff.1 h2
          obtain ⟨hv1, hv2⟩ := cacheLTS_valid hc1 hnd hck
          have hseg : (cacheLTS k).MTr c1 (es1 ++ [e2]) c2 :=
            Cslib.LTS.MTr.comp (cacheLTS k) h1' (Cslib.LTS.MTr.single (cacheLTS k) hc2)
          have hp : CacheEvent.request e0 ∈ c1 := request_mem_of_tr (by omega) hc1
          simp only [List.map_cons] at hmap1 hmap2
          obtain ⟨hreq2, _⟩ := List.cons.inj hmap2
          have hone : 1 ≤ misses (es1 ++ [e2]) := by
            refine one_le_misses hseg hv2 hp (distinct := q :: S) (List.nodup_cons.2 ⟨hqS, hS⟩)
              (by simp [hSl]) fun x hx => ?_
            rcases List.mem_cons.1 hx with rfl | hx
            · right; simp [hreq2]
            · have hxP := hSsub x hx
              rw [← hP, ← hmap1] at hxP
              rcases List.mem_cons.1 hxP with h | h
              · left; exact h
              · right; simp only [List.map_append, List.map_cons, List.map_nil]
                exact List.mem_append_left _ h
          have htail : es.tail = es1 ++ e2 :: es2 := by
            rw [hsplit, hes1, hes2]; rfl
          have hmt : misses es.tail = misses (es1 ++ [e2]) + misses es2 := by
            rw [htail, ← misses_append, List.append_assoc, List.singleton_append]
          have : k * (misses es2 + 1) ≤ k * misses es.tail :=
            Nat.mul_le_mul_left k (by omega)
          simp only [List.tail_cons] at ih
          rw [Nat.mul_add, Nat.mul_one] at this
          omega

/-- **A policy that misses at most `k` times per phase is `k`-competitive**: on every request
sequence it misses at most `k * m + k` times, where `m` counts the misses of any legal trace of
`cacheLTS k` (from any legal cache) serving the same requests. -/
theorem policyMisses_le (step : List α → α → List α) {k : ℕ} (hk : 1 ≤ k)
    (hphase : ∀ c σ : List α, policyMisses step c (phaseSplit k [] σ).1 ≤ k) (c : List α)
    {c0 cf : List α} {es : List (CacheEvent α)} (hes : (cacheLTS k).MTr c0 es cf)
    (hnd : c0.Nodup) (hck : c0.length ≤ k) :
    policyMisses step c (es.map CacheEvent.request) ≤ k * misses es + k := by
  by_cases hσ : es.map CacheEvent.request = []
  · rw [hσ]; simp [policyMisses]
  · have h := policyMisses_le_tail step hk hphase _ (es.map CacheEvent.request) (le_refl _) c c0
      cf es hes hnd hck rfl hσ
    have : misses es.tail ≤ misses es := by
      cases es with
      | nil => exact le_refl _
      | cons e es =>
          simp only [List.tail_cons, misses, List.countP_cons]
          omega
    have := Nat.mul_le_mul_left k this
    omega

/-- LRU is such a policy: `policyMisses` of `lruStep` is `lruMisses`. -/
theorem policyMisses_lruStep (k : ℕ) : policyMisses (lruStep (α := α) k) = lruMisses k := by
  funext c σ
  induction σ generalizing c with
  | nil => rfl
  | cons p σ ih => simp [policyMisses, lruMisses, ih]

/-! ## FIFO -/

/-- One FIFO step with capacity `k` (oldest page first): on a miss the page joins the back of the
queue, and if the cache was full the front page, the one loaded earliest, is evicted. -/
def fifoStep (k : ℕ) (c : List α) (p : α) : List α :=
  if p ∈ c then c else if c.length < k then c ++ [p] else (c ++ [p]).tail

/-- FIFO keeps a legal cache: distinct pages, at most `k` of them. -/
theorem fifoStep_legal {k : ℕ} {c : List α} (hnd : c.Nodup) (hck : c.length ≤ k) (p : α) :
    (fifoStep k c p).Nodup ∧ (fifoStep k c p).length ≤ k := by
  unfold fifoStep
  split_ifs with hp hlt
  · exact ⟨hnd, hck⟩
  · refine ⟨List.nodup_append.2 ⟨hnd, List.nodup_singleton p, ?_⟩, by simp; omega⟩
    simp only [List.mem_singleton]
    rintro a ha b rfl rfl
    exact hp ha
  · have hnd' : (c ++ [p]).Nodup := List.nodup_append.2 ⟨hnd, List.nodup_singleton p, by
      simp only [List.mem_singleton]; rintro a ha b rfl rfl; exact hp ha⟩
    exact ⟨hnd'.sublist (List.tail_sublist _), by simp; omega⟩

omit [DecidableEq α] in
private theorem isSuffix_append_singleton {L c : List α} (h : L <:+ c) (p : α) :
    L ++ [p] <:+ c ++ [p] := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t, by simp⟩

omit [DecidableEq α] in
private theorem isSuffix_tail {L m : List α} (h : L <:+ m) (hlt : L.length < m.length) :
    L <:+ m.tail := by
  obtain ⟨t, rfl⟩ := h
  cases t with
  | nil => simp at hlt
  | cons x t => exact ⟨t, by simp⟩

/-- **FIFO misses at most `k` times per phase.** The pages loaded so far in the phase (`L`, in
load order) stay at the back of the queue: each miss appends one, and an eviction removes the
front, which is not among them while at most `k` pages have been loaded. So a page of the phase is
missed at most once, and a phase has at most `k` distinct pages. -/
theorem fifoMisses_phase (k : ℕ) : ∀ (seen c L σ : List α), L <:+ c → L.Nodup →
    (∀ x ∈ L, x ∈ seen) → seen.Nodup → seen.length ≤ k →
    policyMisses (fifoStep k) c (phaseSplit k seen σ).1 + L.length ≤ k
  | seen, _, L, [], _, hL, hLs, hnd, hk => by
      simp only [phaseSplit, policyMisses, Nat.zero_add]
      exact ((hL.subperm hLs).length_le).trans hk
  | seen, c, L, p :: rest, hsuf, hL, hLs, hnd, hk => by
      have hLlen : L.length ≤ seen.length := (hL.subperm hLs).length_le
      -- the next `seen` contains the old one and `p`
      have step : ∀ seen' : List α, seen'.Nodup → seen'.length ≤ k → (∀ x ∈ seen, x ∈ seen') →
          p ∈ seen' → policyMisses (fifoStep k) c (p :: (phaseSplit k seen' rest).1) + L.length ≤ k
          := by
        intro seen' hnd' hk' hsub hp'
        simp only [policyMisses]
        by_cases hpc : p ∈ c
        · have hstep : fifoStep k c p = c := by simp [fifoStep, hpc]
          simp only [hpc, ↓reduceIte, Nat.zero_add, hstep]
          exact fifoMisses_phase k seen' c L rest hsuf hL (fun x hx => hsub x (hLs x hx)) hnd' hk'
        · have hpL : p ∉ L := fun h => hpc (hsuf.subset h)
          have hL' : (L ++ [p]).Nodup := List.nodup_append.2 ⟨hL, List.nodup_singleton p, by
            simp only [List.mem_singleton]; rintro a ha b rfl rfl; exact hpL ha⟩
          have hLs' : ∀ x ∈ L ++ [p], x ∈ seen' := by
            intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact hsub x (hLs x hx)
            · rw [List.mem_singleton.1 hx]; exact hp'
          have hlen' : (L ++ [p]).length ≤ k := ((hL'.subperm hLs').length_le).trans hk'
          have hsuf' : L ++ [p] <:+ fifoStep k c p := by
            unfold fifoStep
            simp only [hpc, ↓reduceIte]
            split_ifs with hlt
            · exact isSuffix_append_singleton hsuf p
            · refine isSuffix_tail (isSuffix_append_singleton hsuf p) ?_
              simp only [List.length_append, List.length_singleton] at hlen' ⊢
              omega
          have ih := fifoMisses_phase k seen' (fifoStep k c p) (L ++ [p]) rest hsuf' hL' hLs'
            hnd' hk'
          simp only [hpc, ↓reduceIte, List.length_append, List.length_singleton] at ih ⊢
          omega
      simp only [phaseSplit]
      split_ifs with hp hlt
      · have hlen : (p :: seen.erase p).length = seen.length := by
          rw [List.length_cons, List.length_erase_of_mem hp]
          have := List.length_pos_of_mem hp
          omega
        refine step _ (List.nodup_cons.2 ⟨fun h => (List.Nodup.mem_erase_iff hnd).1 h |>.1 rfl,
          hnd.erase p⟩) (by rw [hlen]; exact hk) (fun x hx => ?_) List.mem_cons_self
        by_cases hxp : x = p
        · rw [hxp]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ ((List.Nodup.mem_erase_iff hnd).2 ⟨hxp, hx⟩)
      · exact step _ (List.nodup_cons.2 ⟨hp, hnd⟩) (by simp; omega)
          (fun x hx => List.mem_cons_of_mem _ hx) List.mem_cons_self
      · simp only [policyMisses, Nat.zero_add]
        omega

/-- A legal cache of capacity `k`: distinct pages, at most `k` of them. -/
abbrev LegalCache (α : Type*) (k : ℕ) := {c : List α // c.Nodup ∧ c.length ≤ k}

/-- FIFO, started from a legal cache, keeps a legal cache. -/
theorem fifoCache_legal {k : ℕ} : ∀ (c : List α) (σ : List α), c.Nodup → c.length ≤ k →
    (σ.foldl (fifoStep k) c).Nodup ∧ (σ.foldl (fifoStep k) c).length ≤ k
  | c, [], hnd, hck => ⟨hnd, hck⟩
  | c, p :: σ, hnd, hck => by
      obtain ⟨h1, h2⟩ := fifoStep_legal hnd hck p
      exact fifoCache_legal _ σ h1 h2

/-- FIFO as an online pager (`OnlinePager` of `PagingLowerBound.lean`), on legal caches. -/
def fifoPager (α : Type*) [DecidableEq α] (k : ℕ) : OnlinePager α k where
  State := LegalCache α k
  init := ⟨[], List.nodup_nil, Nat.zero_le k⟩
  cache q := q.1
  step q p := ⟨fifoStep k q.1 p, fifoStep_legal q.2.1 q.2.2 p⟩
  cache_le q := q.2.2

/-- The online pager `fifoPager` misses exactly as `policyMisses (fifoStep k)` counts. -/
theorem fifoPager_misses {k : ℕ} :
    ∀ (q : (fifoPager α k).State) (σ : List α),
      (fifoPager α k).misses q σ = policyMisses (fifoStep k) q.1 σ
  | _, [] => rfl
  | q, p :: σ => by
      simp only [OnlinePager.misses, policyMisses]
      rw [fifoPager_misses _ σ]
      rfl

/-- **FIFO is `k`-competitive** (Sleator and Tarjan): from any legal cache, on every request
sequence the pager `fifoPager` misses at most `k * m + k` times, where `m` counts the misses of
any legal trace with the same capacity from any legal cache. -/
theorem fifoMisses_le {k : ℕ} (hk : 1 ≤ k) (q : (fifoPager α k).State) {c0 cf : List α}
    {es : List (CacheEvent α)} (hes : (cacheLTS k).MTr c0 es cf) (hnd : c0.Nodup)
    (hck : c0.length ≤ k) :
    (fifoPager α k).misses q (es.map CacheEvent.request) ≤ k * misses es + k := by
  rw [fifoPager_misses]
  exact policyMisses_le (fifoStep k) hk (fun c σ => by
    simpa using fifoMisses_phase k [] c [] σ List.nil_suffix List.nodup_nil
      (fun _ h => absurd h List.not_mem_nil) List.nodup_nil (Nat.zero_le k)) q.1 hes hnd hck

/-- **FIFO is `k`-competitive against the offline optimum** (furthest-in-future). -/
theorem fifoMisses_le_furthestInFuture {k : ℕ} (hk : 1 ≤ k) (q : (fifoPager α k).State)
    (requests : List α) {c0 : List α} (hnd : c0.Nodup) (hck : c0.length ≤ k) :
    (fifoPager α k).misses q requests ≤ k * misses (furthestInFuture k requests c0).1 + k := by
  obtain ⟨hlegal, -, -⟩ := furthestInFuture_legal k requests c0 hnd hck
  have := fifoMisses_le hk q hlegal hnd hck
  rwa [furthestInFuture_requests k requests c0 hnd hck] at this

/-- **The ratio `k` is tight for FIFO**: `fifoMisses_le_furthestInFuture` and, from
`not_competitive_of_lt`, for every ratio `c / d < k` some sequence on `k + 1` pages makes FIFO
miss more than `c / d` times the optimum plus `b / d`. -/
theorem fifo_not_competitive_of_lt {k : ℕ} (hk : 1 ≤ k) {c d : ℕ} (hc : c < k * d) (b : ℕ) :
    ∃ σ : List (Fin (k + 1)), c * misses (furthestInFuture k σ []).1 + b <
      d * (fifoPager (Fin (k + 1)) k).misses (fifoPager (Fin (k + 1)) k).init σ :=
  not_competitive_of_lt hk (fifoPager (Fin (k + 1)) k) hc b

end Cslib.Algorithms.Lean.Online.FifoPaging
