/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Online.MarkingPaging
public meta import CSLibExt.Algorithms.Lean.Online.MarkingPaging

/-!
# Marking paging tests

Executed fixtures: on 300 pseudo-random request sequences (up to 6 pages, 40 requests, capacity
`k = 0, …, 4`) and two eviction rules (the first and the last candidate), every eviction removes a
cached page that is unmarked unless the request starts a new phase, marks stay on cached pages,
and `markingPager` counts the misses of `markTrace`; when `k > 0` the requested page is marked
afterwards and no page is missed twice within a phase. Each run throws on a violation. Closed
checks cover each branch of `markStep` (hit, miss with room, eviction, new phase, zero capacity),
capacity one, and a full cache whose only unmarked page must be the victim.
-/

namespace Cslib.Algorithms.Lean.Online.MarkingPaging

open Cslib.Algorithms.Lean.OfflineCaching Cslib.Algorithms.Lean.Online.Paging

/-- The rule that picks the first candidate. -/
private def headRule : EvictionRule ℕ where
  pick := List.head?
  pick_mem := fun h => List.mem_of_mem_head? h
  pick_ne_none := fun h hn => h (List.head?_eq_none_iff.1 hn)

#eval do
  let mut s := 29
  let mut total := 0
  for _ in [0:300] do
    s := (s * 1103515245 + 12345) % 2147483648
    let k := s / 7 % 5
    s := (s * 1103515245 + 12345) % 2147483648
    let pages := s / 7 % 6 + 1
    let mut σ : List ℕ := []
    for _ in [0:40] do
      s := (s * 1103515245 + 12345) % 2147483648
      σ := σ ++ [s / 11 % pages]
    for R in [EvictionRule.last, headRule] do
      let mut st : MarkState ℕ k := MarkState.empty
      let mut missedInPhase : List ℕ := []
      for p in σ do
        let newPhase := decide (StartsPhase st p)
        if newPhase then missedInPhase := []
        match markEvent R st p with
        | .hit q =>
            unless q == p && decide (p ∈ st.cache.1) do throw (IO.userError "hit")
        | .miss q v =>
            unless q == p && decide (p ∉ st.cache.1) do throw (IO.userError "miss")
            if 0 < k && p ∈ missedInPhase then
              throw (IO.userError s!"missed twice in a phase: k = {k}, {σ}")
            missedInPhase := p :: missedInPhase
            if let some v := v then
              unless decide (v ∈ st.cache.1) do throw (IO.userError "victim not cached")
              unless newPhase || decide (v ∉ st.marked) do throw (IO.userError "marked victim")
        st := markStep R st p
        unless k == 0 || decide (p ∈ st.marked) do throw (IO.userError "unmarked request")
        unless decide (∀ q ∈ st.marked, q ∈ st.cache.1) do throw (IO.userError "stray mark")
        unless st.cache.1.Nodup && st.cache.1.length ≤ k do throw (IO.userError "illegal cache")
      let m := (markingPager R k).misses (markingPager R k).init σ
      unless m == misses (markTrace R (MarkState.empty : MarkState ℕ k) σ) do
        throw (IO.userError "pager")
      total := total + m
  IO.println s!"300 sequences x 2 rules: legal victims, marked requests, cached marks, no page \
    missed twice in a phase, pager counts agree; {total} misses in total"

/-! Closed checks: each branch of `markStep` -/

/-- A state from concrete data. -/
private abbrev st (k : ℕ) (c : List ℕ) (m : Finset ℕ) (h₁ : c.Nodup) (h₂ : c.length ≤ k)
    (h₃ : ∀ q ∈ m, q ∈ c) : MarkState ℕ k :=
  ⟨⟨c, h₁, h₂⟩, m, h₃⟩

/-- Two slots holding `1, 0`, with `0` marked. -/
private abbrev s₁ : MarkState ℕ 2 := st 2 [1, 0] {0} (by decide) (by decide) (by decide)

/-- Three slots holding `0`, marked. -/
private abbrev s₂ : MarkState ℕ 3 := st 3 [0] {0} (by decide) (by decide) (by decide)

/-- Two slots holding `0, 1`, with only `0` marked. -/
private abbrev s₃ : MarkState ℕ 2 := st 2 [0, 1] {0} (by decide) (by decide) (by decide)

/-- Two slots holding `1, 0`, both marked. -/
private abbrev s₄ : MarkState ℕ 2 := st 2 [1, 0] {0, 1} (by decide) (by decide) (by decide)

/-- One slot holding `0`, unmarked. -/
private abbrev s₅ : MarkState ℕ 1 := st 1 [0] ∅ (by decide) (by decide) (by decide)

-- a hit marks the page and keeps the cache
example : markEvent EvictionRule.last s₁ 1 = .hit 1 := rfl
example : (markStep EvictionRule.last s₁ 1).cache.1 = [1, 0] := by decide
example : (markStep EvictionRule.last s₁ 1).marked = {0, 1} := by decide

-- a miss with room loads and marks the page
example : markEvent EvictionRule.last s₂ 1 = .miss 1 none := rfl
example : (markStep EvictionRule.last s₂ 1).cache.1 = [1, 0] := by decide
example : (markStep EvictionRule.last s₂ 1).marked = {0, 1} := by decide

-- a full cache evicts its only unmarked page `1` under either rule, never the marked page `0`
example : markEvent EvictionRule.last s₃ 2 = .miss 2 (some 1) := rfl
example : markEvent headRule s₃ 2 = .miss 2 (some 1) := rfl
example : (markStep headRule s₃ 2).cache.1 = [2, 0] := by decide
example : (markStep headRule s₃ 2).marked = {0, 2} := by decide

-- all pages marked: a new phase erases the marks, and the rule's choice decides the victim
example : StartsPhase s₄ 2 := by decide
example : ¬StartsPhase s₃ 2 := by decide
example : markEvent EvictionRule.last s₄ 2 = .miss 2 (some 0) := rfl
example : markEvent headRule s₄ 2 = .miss 2 (some 1) := rfl
example : (markStep headRule s₄ 2).marked = {2} := by decide

-- capacity one: a miss replaces the page instead of growing the cache
example : markEvent EvictionRule.last s₅ 1 = .miss 1 (some 0) := rfl
example : (markStep EvictionRule.last s₅ 1).cache.1 = [1] := by decide

-- zero capacity: every request misses and nothing is cached
example : markEvent EvictionRule.last (MarkState.empty : MarkState ℕ 0) 0 = .miss 0 none := rfl
example : (markStep EvictionRule.last (MarkState.empty : MarkState ℕ 0) 0).cache.1 = [] := by
  decide

-- a short run: the rule changes the cost, `0 1 0 2 0 1` with two slots
example : (markingPager EvictionRule.last 2).misses (markingPager EvictionRule.last 2).init
    [0, 1, 0, 2, 0, 1] = 5 := by decide
example : (markingPager headRule 2).misses (markingPager headRule 2).init
    [0, 1, 0, 2, 0, 1] = 4 := by decide

/-! Closed checks: theorem instances -/

example (σ : List ℕ) :
    (cacheLTS 3).MTr [] (markTrace EvictionRule.last (MarkState.empty : MarkState ℕ 3) σ)
      (markRun EvictionRule.last (MarkState.empty : MarkState ℕ 3) σ).cache.1 :=
  (markTrace_spec EvictionRule.last MarkState.empty σ).1

example (s : MarkState ℕ 3) (p : ℕ) (σ : List ℕ)
    (h : NoNewPhase headRule (markStep headRule s p) σ) :
    p ∈ (markRun headRule (markStep headRule s p) σ).cache.1 :=
  mem_cache_markRun_markStep headRule s p (by decide) σ h

-- as an online pager it inherits the lower bound: ratio `5 / 2 < 3` fails on 4 pages
example (b : ℕ) : ∃ σ : List (Fin 4), 5 * misses (furthestInFuture 3 σ []).1 + b <
    2 * (markingPager EvictionRule.last 3).misses (markingPager EvictionRule.last 3).init σ :=
  not_competitive_of_lt (by decide) _ (by decide) b

#print axioms markTrace_spec
#print axioms mem_cache_markRun_markStep
#print axioms markEvent_victim

end Cslib.Algorithms.Lean.Online.MarkingPaging
