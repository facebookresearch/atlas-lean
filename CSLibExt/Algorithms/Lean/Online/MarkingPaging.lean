/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Online.FifoPaging
public import Mathlib.Data.Finset.Insert

/-!
# Marking paging algorithms

The marking algorithm of Fiat, Karp, Luby, McGeoch, Sleator and Young (*Competitive paging
algorithms*, Journal of Algorithms 12, 1991): every request marks its page; a miss on a full
cache whose pages are all marked starts a new phase by erasing every mark; a miss on a full cache
then evicts an unmarked page, and the requested page is loaded and marked. Fiat et al. evict a
uniformly random unmarked page. Here an eviction rule (`EvictionRule`) picks the victim among the
unmarked cached pages, so each rule gives a deterministic marking algorithm.

Main results:

* `MarkState`, `markStep`: a state is a legal cache (`LegalCache`) whose marked pages are cached,
  and each step returns such a state; `markEvent_victim`: an evicted page was cached and, unless
  the request started a new phase (`StartsPhase`), unmarked.
* `markStep_tr`, `markTrace_spec`: each step is a transition of `cacheLTS k`, and the events on a
  request sequence form a legal trace that serves exactly the requests and misses exactly as often
  as the online pager `markingPager`.
* `marked_subset_markRun`, `mem_cache_markRun_markStep`: while no request starts a new phase
  (`NoNewPhase`), marks only accumulate and marked pages stay cached, so after a request for `p`
  every later request for `p` in the same phase is a hit.

Zero capacity caches nothing and misses every request, as `cacheLTS 0` requires. The competitive
upper bounds (`k` for deterministic marking algorithms; `2 H_k` for the randomized one, by Fiat et
al.) are not proved here.

## Cost model

The cost is the number of misses; there is no computation to charge.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Online.MarkingPaging

open Cslib.Algorithms.Lean.OfflineCaching Cslib.Algorithms.Lean.Online.Paging
  Cslib.Algorithms.Lean.Online.FifoPaging

/-! ## States and eviction rules -/

/-- A state of a marking algorithm with capacity `k`: a legal cache and its marked pages. -/
structure MarkState (α : Type*) (k : ℕ) where
  /-- The cached pages: distinct, at most `k` of them. -/
  cache : LegalCache α k
  /-- The marked pages. -/
  marked : Finset α
  /-- Only cached pages are marked. -/
  marked_sub : ∀ q ∈ marked, q ∈ cache.1

/-- The empty state: no cached and no marked pages. -/
def MarkState.empty {α : Type*} {k : ℕ} : MarkState α k :=
  ⟨⟨[], List.nodup_nil, Nat.zero_le k⟩, ∅, fun _ h => absurd h (Finset.notMem_empty _)⟩

/-- An eviction rule picks one page from a nonempty list of candidates. -/
structure EvictionRule (α : Type*) where
  /-- The chosen candidate. -/
  pick : List α → Option α
  /-- The choice is a candidate. -/
  pick_mem : ∀ {l : List α} {v : α}, pick l = some v → v ∈ l
  /-- A nonempty candidate list has a choice. -/
  pick_ne_none : ∀ {l : List α}, l ≠ [] → pick l ≠ none

/-- The rule that picks the last candidate. -/
def EvictionRule.last {α : Type*} : EvictionRule α where
  pick := List.getLast?
  pick_mem := fun h => List.mem_of_getLast? h
  pick_ne_none := fun h hn => h (List.getLast?_eq_none_iff.1 hn)

variable {α : Type*} [DecidableEq α] {k : ℕ}

/-- The marks in force when a miss meets a full cache `c` with marks `m`: if every cached page is
marked, a new phase starts and every mark is erased. -/
def phaseMarks (c : List α) (m : Finset α) : Finset α :=
  if ∀ q ∈ c, q ∈ m then ∅ else m

/-- The pages of `c` outside `m`, in cache order. -/
def unmarked (c : List α) (m : Finset α) : List α :=
  c.filter fun q => q ∉ m

theorem phaseMarks_subset (c : List α) (m : Finset α) : phaseMarks c m ⊆ m := by
  unfold phaseMarks
  split_ifs
  · exact Finset.empty_subset m
  · exact Finset.Subset.refl m

theorem mem_unmarked {c : List α} {m : Finset α} {q : α} :
    q ∈ unmarked c m ↔ q ∈ c ∧ q ∉ m := by
  simp [unmarked]

/-- After the phase check, a nonempty cache has an unmarked page. -/
theorem unmarked_phaseMarks_ne_nil {c : List α} (m : Finset α) (hc : c ≠ []) :
    unmarked c (phaseMarks c m) ≠ [] := by
  unfold phaseMarks
  split_ifs with h
  · simpa [unmarked] using hc
  · obtain ⟨q, hq, hqm⟩ := not_forall₂.1 h
    exact List.ne_nil_of_mem (mem_unmarked.2 ⟨hq, hqm⟩)

omit [DecidableEq α] in
/-- A full cache of positive capacity is nonempty. -/
theorem cache_ne_nil_of_full (s : MarkState α k) (hfull : ¬s.cache.1.length < k) (hk : k ≠ 0) :
    s.cache.1 ≠ [] := by
  intro h
  rw [h, List.length_nil] at hfull
  omega

/-- The page a miss on a full cache evicts: `R`'s pick among the pages unmarked after the phase
check. -/
def victim (R : EvictionRule α) (s : MarkState α k) (hfull : ¬s.cache.1.length < k)
    (hk : k ≠ 0) : α :=
  (R.pick (unmarked s.cache.1 (phaseMarks s.cache.1 s.marked))).get
    (Option.isSome_iff_ne_none.2
      (R.pick_ne_none (unmarked_phaseMarks_ne_nil _ (cache_ne_nil_of_full s hfull hk))))

theorem victim_mem_unmarked (R : EvictionRule α) (s : MarkState α k)
    (hfull : ¬s.cache.1.length < k) (hk : k ≠ 0) :
    victim R s hfull hk ∈ unmarked s.cache.1 (phaseMarks s.cache.1 s.marked) :=
  R.pick_mem (Option.some_get _).symm

/-! ## One step -/

/-- Serve a request. A hit marks the page. A miss with room loads and marks the page. A miss
with zero capacity caches nothing. A miss on a full cache starts a new phase if every cached page
is marked, evicts `victim R s`, then loads and marks the page. -/
def markStep (R : EvictionRule α) (s : MarkState α k) (p : α) : MarkState α k :=
  if hp : p ∈ s.cache.1 then
    ⟨s.cache, insert p s.marked, fun q hq => by
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact hp
      · exact s.marked_sub q hq⟩
  else if hfull : s.cache.1.length < k then
    ⟨⟨p :: s.cache.1, List.nodup_cons.2 ⟨hp, s.cache.2.1⟩, by
        rw [List.length_cons]
        omega⟩,
      insert p s.marked, fun q hq => by
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (s.marked_sub q hq)⟩
  else if hk : k = 0 then s
  else
    ⟨⟨p :: s.cache.1.erase (victim R s hfull hk),
        List.nodup_cons.2 ⟨fun h => hp (List.mem_of_mem_erase h), s.cache.2.1.erase _⟩, by
        have := s.cache.2.2
        rw [List.length_cons,
          List.length_erase_of_mem (mem_unmarked.1 (victim_mem_unmarked R s hfull hk)).1]
        omega⟩,
      insert p (phaseMarks s.cache.1 s.marked), fun q hq => by
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact List.mem_cons_self
      · refine List.mem_cons_of_mem _ ((List.mem_erase_of_ne ?_).2
          (s.marked_sub q (phaseMarks_subset _ _ hq)))
        rintro rfl
        exact (mem_unmarked.1 (victim_mem_unmarked R s hfull hk)).2 hq⟩

/-- The cache event of `markStep`: a hit, a miss without eviction (with room, or with zero
capacity), or a miss evicting `victim R s`. -/
def markEvent (R : EvictionRule α) (s : MarkState α k) (p : α) : CacheEvent α :=
  if p ∈ s.cache.1 then .hit p
  else if hfull : s.cache.1.length < k then .miss p none
  else if hk : k = 0 then .miss p none
  else .miss p (some (victim R s hfull hk))

/-- Serving `p` starts a new phase: it misses a full cache of positive capacity whose pages are
all marked. -/
def StartsPhase (s : MarkState α k) (p : α) : Prop :=
  p ∉ s.cache.1 ∧ k ≤ s.cache.1.length ∧ 0 < k ∧ ∀ q ∈ s.cache.1, q ∈ s.marked

instance (s : MarkState α k) (p : α) : Decidable (StartsPhase s p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem markEvent_request (R : EvictionRule α) (s : MarkState α k) (p : α) :
    (markEvent R s p).request = p := by
  unfold markEvent
  split_ifs <;> rfl

theorem markEvent_isMiss (R : EvictionRule α) (s : MarkState α k) (p : α) :
    (markEvent R s p).isMiss = !decide (p ∈ s.cache.1) := by
  unfold markEvent
  split_ifs with hp <;> simp [hp]

/-- **A marking algorithm never evicts a marked page**: an evicted page was cached and, unless
the request started a new phase, which erases every mark, it was unmarked. -/
theorem markEvent_victim (R : EvictionRule α) (s : MarkState α k) (p : α) {v : α}
    (hv : markEvent R s p = .miss p (some v)) :
    v ∈ s.cache.1 ∧ (¬StartsPhase s p → v ∉ s.marked) := by
  unfold markEvent at hv
  by_cases hp : p ∈ s.cache.1
  · rw [ite_eq_left hp] at hv
    exact absurd hv (by simp)
  rw [ite_eq_right hp] at hv
  by_cases hfull : s.cache.1.length < k
  · rw [dite_eq_left hfull] at hv
    exact absurd hv (by simp)
  rw [dite_eq_right hfull] at hv
  by_cases hk : k = 0
  · rw [dite_eq_left hk] at hv
    exact absurd hv (by simp)
  rw [dite_eq_right hk] at hv
  obtain rfl : victim R s hfull hk = v := by
    simpa using hv
  refine ⟨(mem_unmarked.1 (victim_mem_unmarked R s hfull hk)).1, fun hnew => ?_⟩
  have hnot : ¬∀ q ∈ s.cache.1, q ∈ s.marked := fun hall =>
    hnew ⟨hp, by omega, Nat.pos_of_ne_zero hk, hall⟩
  have h := (mem_unmarked.1 (victim_mem_unmarked R s hfull hk)).2
  rwa [phaseMarks, ite_eq_right hnot] at h

/-- A hit keeps the cache and marks the page. -/
theorem markStep_of_mem (R : EvictionRule α) (s : MarkState α k) {p : α} (hp : p ∈ s.cache.1) :
    (markStep R s p).cache = s.cache ∧ (markStep R s p).marked = insert p s.marked := by
  unfold markStep
  rw [dite_eq_left hp]
  exact ⟨rfl, rfl⟩

/-- A request that starts a new phase leaves exactly its page marked. -/
theorem markStep_marked_of_startsPhase (R : EvictionRule α) (s : MarkState α k) {p : α}
    (h : StartsPhase s p) : (markStep R s p).marked = {p} := by
  obtain ⟨hp, hfull, hk, hall⟩ := h
  unfold markStep
  rw [dite_eq_right hp, dite_eq_right (by omega), dite_eq_right (by omega)]
  change insert p (phaseMarks s.cache.1 s.marked) = {p}
  rw [phaseMarks, ite_eq_left hall]
  simp

/-- With positive capacity, the requested page is marked after the step. -/
theorem mem_marked_markStep (R : EvictionRule α) (s : MarkState α k) (p : α) (hk : 0 < k) :
    p ∈ (markStep R s p).marked := by
  unfold markStep
  by_cases hp : p ∈ s.cache.1
  · rw [dite_eq_left hp]
    exact Finset.mem_insert_self p _
  rw [dite_eq_right hp]
  by_cases hfull : s.cache.1.length < k
  · rw [dite_eq_left hfull]
    exact Finset.mem_insert_self p _
  rw [dite_eq_right hfull, dite_eq_right (by omega)]
  exact Finset.mem_insert_self p _

/-- Unless it starts a new phase, a step keeps every mark. -/
theorem marked_subset_markStep (R : EvictionRule α) (s : MarkState α k) (p : α)
    (h : ¬StartsPhase s p) : s.marked ⊆ (markStep R s p).marked := by
  unfold markStep
  by_cases hp : p ∈ s.cache.1
  · rw [dite_eq_left hp]
    exact Finset.subset_insert p _
  rw [dite_eq_right hp]
  by_cases hfull : s.cache.1.length < k
  · rw [dite_eq_left hfull]
    exact Finset.subset_insert p _
  rw [dite_eq_right hfull]
  by_cases hk : k = 0
  · rw [dite_eq_left hk]
  rw [dite_eq_right hk]
  have hnot : ¬∀ q ∈ s.cache.1, q ∈ s.marked := fun hall =>
    h ⟨hp, by omega, Nat.pos_of_ne_zero hk, hall⟩
  simp only [phaseMarks, ite_eq_right hnot]
  exact Finset.subset_insert p _

/-- **Each step is a legal transition** of the cache system `cacheLTS k`. -/
theorem markStep_tr (R : EvictionRule α) (s : MarkState α k) (p : α) :
    (cacheLTS k).Tr s.cache.1 (markEvent R s p) (markStep R s p).cache.1 := by
  unfold markEvent markStep
  by_cases hp : p ∈ s.cache.1
  · rw [ite_eq_left hp, dite_eq_left hp]
    exact ⟨hp, List.Perm.refl _⟩
  rw [ite_eq_right hp, dite_eq_right hp]
  by_cases hfull : s.cache.1.length < k
  · rw [dite_eq_left hfull, dite_eq_left hfull]
    exact ⟨hp, Or.inr ⟨hfull, List.Perm.refl _⟩⟩
  rw [dite_eq_right hfull, dite_eq_right hfull]
  by_cases hk : k = 0
  · rw [dite_eq_left hk, dite_eq_left hk]
    have hnil : s.cache.1 = [] := List.eq_nil_of_length_eq_zero (by have := s.cache.2.2; omega)
    exact ⟨hp, Or.inl ⟨hk, hnil, hnil⟩⟩
  rw [dite_eq_right hk, dite_eq_right hk]
  exact ⟨Nat.pos_of_ne_zero hk, hp, by have := s.cache.2.2; omega,
    (mem_unmarked.1 (victim_mem_unmarked R s hfull hk)).1, List.Perm.refl _⟩

/-! ## Request sequences -/

/-- The state after serving a request sequence. -/
def markRun (R : EvictionRule α) (s : MarkState α k) (σ : List α) : MarkState α k :=
  σ.foldl (markStep R) s

/-- The events emitted on a request sequence. -/
def markTrace (R : EvictionRule α) : MarkState α k → List α → List (CacheEvent α)
  | _, [] => []
  | s, p :: σ => markEvent R s p :: markTrace R (markStep R s p) σ

/-- A marking algorithm as an online pager, started from the empty state. -/
def markingPager (R : EvictionRule α) (k : ℕ) : OnlinePager α k where
  State := MarkState α k
  init := MarkState.empty
  cache s := s.cache.1
  step := markStep R
  cache_le s := s.cache.2.2

/-- **A marking algorithm is a legal cache manager**: its events form a trace of `cacheLTS k`
from the current cache to the final one, serve exactly the requests, and miss exactly as often
as `markingPager`. -/
theorem markTrace_spec (R : EvictionRule α) : ∀ (s : MarkState α k) (σ : List α),
    (cacheLTS k).MTr s.cache.1 (markTrace R s σ) (markRun R s σ).cache.1 ∧
      (markTrace R s σ).map CacheEvent.request = σ ∧
      misses (markTrace R s σ) = (markingPager R k).misses s σ
  | s, [] => ⟨Cslib.LTS.MTr.refl, rfl, rfl⟩
  | s, p :: σ => by
      obtain ⟨ih1, ih2, ih3⟩ := markTrace_spec R (markStep R s p) σ
      refine ⟨Cslib.LTS.MTr.stepL (markStep_tr R s p) ih1, ?_, ?_⟩
      · simp only [markTrace, List.map_cons, ih2, markEvent_request]
      · simp only [markTrace, misses, OnlinePager.misses] at ih3 ⊢
        rw [List.countP_cons, ih3, markEvent_isMiss]
        change _ = (if p ∈ s.cache.1 then 0 else 1) + (markingPager R k).misses (markStep R s p) σ
        by_cases hp : p ∈ s.cache.1
        · simp [hp]
        · simp [hp]
          omega

/-- No request of `σ`, served from `s`, starts a new phase. -/
def NoNewPhase (R : EvictionRule α) : MarkState α k → List α → Prop
  | _, [] => True
  | s, p :: σ => ¬StartsPhase s p ∧ NoNewPhase R (markStep R s p) σ

/-- **Within a phase marks only accumulate.** -/
theorem marked_subset_markRun (R : EvictionRule α) : ∀ (s : MarkState α k) (σ : List α),
    NoNewPhase R s σ → s.marked ⊆ (markRun R s σ).marked
  | _, [], _ => Finset.Subset.refl _
  | s, p :: σ, ⟨h, hσ⟩ =>
      (marked_subset_markStep R s p h).trans (marked_subset_markRun R (markStep R s p) σ hσ)

/-- **Marked pages stay cached within a phase.** -/
theorem mem_cache_markRun (R : EvictionRule α) (s : MarkState α k) (σ : List α)
    (h : NoNewPhase R s σ) {q : α} (hq : q ∈ s.marked) : q ∈ (markRun R s σ).cache.1 :=
  (markRun R s σ).marked_sub q (marked_subset_markRun R s σ h hq)

/-- **A page is missed at most once per phase**: with positive capacity, after a request for `p`
the page stays cached until a request starts a new phase, so every later request for `p` in the
same phase is a hit. -/
theorem mem_cache_markRun_markStep (R : EvictionRule α) (s : MarkState α k) (p : α) (hk : 0 < k)
    (σ : List α) (h : NoNewPhase R (markStep R s p) σ) :
    p ∈ (markRun R (markStep R s p) σ).cache.1 :=
  mem_cache_markRun R _ σ h (mem_marked_markStep R s p hk)

end Cslib.Algorithms.Lean.Online.MarkingPaging
