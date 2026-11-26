/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Scheduling.ProjectNetwork.CriticalPath
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Critical-path witness checks

Concrete consumers of `CSLibExt.Scheduling.ProjectNetwork.CriticalPath`: a join with a unique
critical chain and its invalid controls, two tied critical paths, a zero-duration milestone on the
witness, the empty table, an all-zero table, and two disconnected jobs. Elaboration checks, not
results.
-/

namespace CSLibExtTest.Scheduling.ProjectNetwork.CriticalPath

open Cslib.Scheduling.ProjectNetwork MathlibExt.Combinatorics.Graph.ArcNetwork

macro "walk_tac" : tactic =>
  `(tactic| (repeat (first | exact walk_nil | refine walk_cons_mk rfl ?_)))

private theorem isAcyclic_of_lt {n : ℕ} {G : Digraph (Fin n)} (h : ∀ a b, G.Adj a b → a < b) :
    G.IsAcyclic := by
  intro v hv
  have key : ∀ a b, Relation.TransGen G.Adj a b → a < b := by
    intro a b hab
    induction hab with
    | single h' => exact h _ _ h'
    | tail _ h' ih => exact lt_trans ih (h _ _ h')
  exact lt_irrefl v (key v v hv)

/-! ### Join `0 → 2`, `1 → 2`, durations `3, 5, 2`: unique critical chain `[1, 2]` -/

def gJoin : Digraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)

instance : DecidableRel gJoin.Adj := fun i j =>
  inferInstanceAs (Decidable ((i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)))

/-- Earliest event dates of the join: starts `0, 0, 5`, finishes `3, 5, 7`, sink `7`. -/
def τJoin : SplitEvent (Fin 3) → ℕ
  | .source => 0
  | .sink => 7
  | .input j => ![0, 0, 5] j
  | .output j => ![3, 5, 7] j

private theorem acycJoin : gJoin.IsAcyclic := isAcyclic_of_lt (by decide)

private theorem hτJoin :
    IsFeasibleSchedule (splitTail gJoin) (splitHead gJoin) (splitDuration gJoin ![3, 5, 2])
      τJoin := by
  intro e
  cases e with
  | job j => fin_cases j <;> decide
  | precedence i j h => revert h; fin_cases i <;> fin_cases j <;> decide
  | fromSource j h => revert h; fin_cases j <;> decide
  | toSink j h => revert h; fin_cases j <;> decide
  | sourceSink => decide

private theorem hwalkJoin : ∀ v, ∃ l, IsArcWalk (splitTail gJoin) (splitHead gJoin) .source v l ∧
    (l.map (splitDuration gJoin ![3, 5, 2])).sum = τJoin v := by
  intro v
  rcases v with _ | _ | j | j
  · exact ⟨[], walk_nil, rfl⟩
  · exact ⟨[.fromSource 1 (by decide), .job 1, .precedence 1 2 (by decide), .job 2,
      .toSink 2 (by decide)], by walk_tac, by decide⟩
  · fin_cases j
    · exact ⟨[.fromSource 0 (by decide)], by walk_tac, by decide⟩
    · exact ⟨[.fromSource 1 (by decide)], by walk_tac, by decide⟩
    · exact ⟨[.fromSource 1 (by decide), .job 1, .precedence 1 2 (by decide)], by walk_tac,
        by decide⟩
  · fin_cases j
    · exact ⟨[.fromSource 0 (by decide), .job 0], by walk_tac, by decide⟩
    · exact ⟨[.fromSource 1 (by decide), .job 1], by walk_tac, by decide⟩
    · exact ⟨[.fromSource 1 (by decide), .job 1, .precedence 1 2 (by decide), .job 2],
        by walk_tac, by decide⟩

/-- The certificate through job `1`. -/
def lJoin : List (SplitArc gJoin) :=
  [.fromSource 1 (by decide), .job 1, .precedence 1 2 (by decide), .job 2, .toSink 2 (by decide)]

private theorem hlJoin : IsArcWalk (splitTail gJoin) (splitHead gJoin) .source .sink lJoin := by
  unfold lJoin
  walk_tac

/-- The certificate's job sequence `[1, 2]` is a directed path from start job `1` to finish job
`2`; its duration `7` is the earliest project finish; it is not the declared arc. -/
example : lJoin.filterMap SplitArc.job? = [1, 2] ∧ ([1, 2] : List (Fin 3)) ∈ gJoin.paths ∧
    (∀ i, ¬ gJoin.Adj i 1) ∧ (∀ k, ¬ gJoin.Adj 2 k) ∧
    (([1, 2] : List (Fin 3)).map ![3, 5, 2]).sum = 7 ∧
    projectFinish ![3, 5, 2] (fun j => τJoin (.input j)) = 7 ∧ lJoin ≠ [.sourceSink] := by
  have hdur : (lJoin.map (splitDuration gJoin ![3, 5, 2])).sum = τJoin .sink := by decide
  obtain ⟨hp, hs, hf, hsum, he⟩ :=
    mem_paths_filterMap_job?_of_sum_eq_sink acycJoin hτJoin hwalkJoin hlJoin hdur
  have hjobs : lJoin.filterMap SplitArc.job? = [1, 2] := rfl
  rw [hjobs] at hp hs hf hsum he
  refine ⟨hjobs, hp, hs 1 rfl, hf 2 rfl, by decide, ?_, fun h => absurd (he.mpr h) (by simp)⟩
  rw [← hsum]
  decide

/-- Uniqueness: every certificate of the join has the job sequence `[1, 2]`. -/
example : ∀ l : List (SplitArc gJoin),
    IsArcWalk (splitTail gJoin) (splitHead gJoin) .source .sink l →
    (l.map (splitDuration gJoin ![3, 5, 2])).sum = τJoin .sink →
    l.filterMap SplitArc.job? = [1, 2] := by
  intro l hl hdur
  obtain ⟨⟨hc, hnd⟩, hs, hf, hsum, -⟩ :=
    mem_paths_filterMap_job?_of_sum_eq_sink acycJoin hτJoin hwalkJoin hl hdur
  have hpf : projectFinish ![3, 5, 2] (fun j => τJoin (.input j)) = 7 := by decide
  rw [hpf] at hsum
  generalize l.filterMap SplitArc.job? = c at hc hnd hs hf hsum ⊢
  have hlen : c.length ≤ 3 := by simpa using hnd.length_le_card
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨e, _ | ⟨x, rest⟩⟩⟩⟩
  · simp at hsum
  · fin_cases a <;> revert hc hs hf hsum <;> decide
  · fin_cases a <;> fin_cases b <;> revert hc hs hf hsum <;> decide
  · fin_cases a <;> fin_cases b <;> fin_cases e <;> revert hc hs hf hsum <;> decide
  · simp at hlen

/-- A non-attained walk (through job `0`, duration `5`) is not a certificate: its job sequence
lasts `5`, not the earliest project finish `7`; the declared arc lasts `0`. -/
example : IsArcWalk (splitTail gJoin) (splitHead gJoin) .source .sink
      [.fromSource 0 (by decide), .job 0, .precedence 0 2 (by decide), .job 2,
        .toSink 2 (by decide)] ∧
    ([.fromSource 0 (by decide), .job 0, .precedence 0 2 (by decide), .job 2,
        .toSink 2 (by decide)].map (splitDuration gJoin ![3, 5, 2])).sum = 5 ∧
    (([.fromSource 0 (by decide), .job 0, .precedence 0 2 (by decide), .job 2,
        .toSink 2 (by decide)] : List (SplitArc gJoin)).filterMap SplitArc.job? = [0, 2]) ∧
    (([0, 2] : List (Fin 3)).map ![3, 5, 2]).sum ≠
      projectFinish ![3, 5, 2] (fun j => τJoin (.input j)) ∧
    ([.sourceSink].map (splitDuration gJoin ![3, 5, 2])).sum ≠ τJoin .sink :=
  ⟨by walk_tac, by decide, rfl, by decide, by decide⟩

/-- A job list that is not a precedence chain is not a directed path and is the job sequence of
no source-to-sink walk. -/
example : ¬ ([0, 1] : List (Fin 3)).IsChain gJoin.Adj ∧ ([0, 1] : List (Fin 3)) ∉ gJoin.paths ∧
    ¬ ([2, 0] : List (Fin 3)).IsChain gJoin.Adj ∧
    ∀ l : List (SplitArc gJoin), IsArcWalk (splitTail gJoin) (splitHead gJoin) .source .sink l →
      l.filterMap SplitArc.job? ≠ [0, 1] := by
  refine ⟨by decide, fun h => absurd h.1 (by decide), by decide, fun l hl h => ?_⟩
  have := (isChain_filterMap_job?_of_isArcWalk hl).1
  rw [h] at this
  exact absurd this (by decide)

/-- A shorter start-to-finish chain is a directed path but not critical: `[0, 2]` lasts `5`, so it
is the job sequence of no certificate. -/
example : ([0, 2] : List (Fin 3)) ∈ gJoin.paths ∧ (∀ i, ¬ gJoin.Adj i 0) ∧
    (∀ k, ¬ gJoin.Adj 2 k) ∧ (([0, 2] : List (Fin 3)).map ![3, 5, 2]).sum = 5 ∧
    ∀ l : List (SplitArc gJoin), IsArcWalk (splitTail gJoin) (splitHead gJoin) .source .sink l →
      (l.map (splitDuration gJoin ![3, 5, 2])).sum = τJoin .sink →
      l.filterMap SplitArc.job? ≠ [0, 2] := by
  refine ⟨⟨by decide, by decide⟩, by decide, by decide, by decide, fun l hl hdur h => ?_⟩
  have := (mem_paths_filterMap_job?_of_sum_eq_sink acycJoin hτJoin hwalkJoin hl hdur).2.2.2.1
  rw [h] at this
  revert this
  decide

/-- Positive durations: no certificate of the join has the empty job sequence. -/
example : ¬ ∃ l, IsArcWalk (splitTail gJoin) (splitHead gJoin) .source .sink l ∧
    (l.map (splitDuration gJoin ![3, 5, 2])).sum = τJoin .sink ∧
    l.filterMap SplitArc.job? = [] := fun h =>
  absurd ((exists_isArcWalk_sum_eq_sink_filterMap_job?_eq_nil_iff acycJoin hτJoin hwalkJoin).mp h 0)
    (by decide)

/-! ### Tie `0 → 2`, `1 → 2`, durations `4, 4, 2`: either critical path is a witness -/

def τTie : SplitEvent (Fin 3) → ℕ
  | .source => 0
  | .sink => 6
  | .input j => ![0, 0, 4] j
  | .output j => ![4, 4, 6] j

private theorem hτTie :
    IsFeasibleSchedule (splitTail gJoin) (splitHead gJoin) (splitDuration gJoin ![4, 4, 2])
      τTie := by
  intro e
  cases e with
  | job j => fin_cases j <;> decide
  | precedence i j h => revert h; fin_cases i <;> fin_cases j <;> decide
  | fromSource j h => revert h; fin_cases j <;> decide
  | toSink j h => revert h; fin_cases j <;> decide
  | sourceSink => decide

private theorem hwalkTie : ∀ v, ∃ l, IsArcWalk (splitTail gJoin) (splitHead gJoin) .source v l ∧
    (l.map (splitDuration gJoin ![4, 4, 2])).sum = τTie v := by
  intro v
  rcases v with _ | _ | j | j
  · exact ⟨[], walk_nil, rfl⟩
  · exact ⟨[.fromSource 0 (by decide), .job 0, .precedence 0 2 (by decide), .job 2,
      .toSink 2 (by decide)], by walk_tac, by decide⟩
  · fin_cases j
    · exact ⟨[.fromSource 0 (by decide)], by walk_tac, by decide⟩
    · exact ⟨[.fromSource 1 (by decide)], by walk_tac, by decide⟩
    · exact ⟨[.fromSource 0 (by decide), .job 0, .precedence 0 2 (by decide)], by walk_tac,
        by decide⟩
  · fin_cases j
    · exact ⟨[.fromSource 0 (by decide), .job 0], by walk_tac, by decide⟩
    · exact ⟨[.fromSource 1 (by decide), .job 1], by walk_tac, by decide⟩
    · exact ⟨[.fromSource 0 (by decide), .job 0, .precedence 0 2 (by decide), .job 2],
        by walk_tac, by decide⟩

/-- Both tied certificates qualify: the witnesses `[0, 2]` and `[1, 2]` are directed paths whose
duration `6` is the earliest project finish. -/
example : ([0, 2] : List (Fin 3)) ∈ gJoin.paths ∧ ([1, 2] : List (Fin 3)) ∈ gJoin.paths ∧
    (([0, 2] : List (Fin 3)).map ![4, 4, 2]).sum =
      projectFinish ![4, 4, 2] (fun j => τTie (.input j)) ∧
    (([1, 2] : List (Fin 3)).map ![4, 4, 2]).sum =
      projectFinish ![4, 4, 2] (fun j => τTie (.input j)) ∧
    projectFinish ![4, 4, 2] (fun j => τTie (.input j)) = 6 := by
  have hA := mem_paths_filterMap_job?_of_sum_eq_sink acycJoin hτTie hwalkTie
    (l := [.fromSource 0 (by decide), .job 0, .precedence 0 2 (by decide), .job 2,
      .toSink 2 (by decide)]) (by walk_tac) (by decide)
  have hB := mem_paths_filterMap_job?_of_sum_eq_sink acycJoin hτTie hwalkTie
    (l := [.fromSource 1 (by decide), .job 1, .precedence 1 2 (by decide), .job 2,
      .toSink 2 (by decide)]) (by walk_tac) (by decide)
  exact ⟨hA.1, hB.1, hA.2.2.2.1, hB.2.2.2.1, by decide⟩

/-! ### Milestone chain `0 → 1 → 2`, durations `4, 0, 3`: the milestone stays on the witness -/

def gChain : Digraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

instance : DecidableRel gChain.Adj := fun i j =>
  inferInstanceAs (Decidable ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)))

def τChain : SplitEvent (Fin 3) → ℕ
  | .source => 0
  | .sink => 7
  | .input j => ![0, 4, 4] j
  | .output j => ![4, 4, 7] j

example : ([0, 1, 2] : List (Fin 3)) ∈ gChain.paths ∧ (1 : Fin 3) ∈ ([0, 1, 2] : List (Fin 3)) ∧
    (![4, 0, 3] : Fin 3 → ℕ) 1 = 0 ∧
    (([0, 1, 2] : List (Fin 3)).map ![4, 0, 3]).sum = 4 + 0 + 3 ∧
    (([0, 1, 2] : List (Fin 3)).map ![4, 0, 3]).sum =
      projectFinish ![4, 0, 3] (fun j => τChain (.input j)) := by
  have hτ : IsFeasibleSchedule (splitTail gChain) (splitHead gChain)
      (splitDuration gChain ![4, 0, 3]) τChain := by
    intro e
    cases e with
    | job j => fin_cases j <;> decide
    | precedence i j h => revert h; fin_cases i <;> fin_cases j <;> decide
    | fromSource j h => revert h; fin_cases j <;> decide
    | toSink j h => revert h; fin_cases j <;> decide
    | sourceSink => decide
  have hwalk : ∀ v, ∃ l, IsArcWalk (splitTail gChain) (splitHead gChain) .source v l ∧
      (l.map (splitDuration gChain ![4, 0, 3])).sum = τChain v := by
    intro v
    rcases v with _ | _ | j | j
    · exact ⟨[], walk_nil, rfl⟩
    · exact ⟨[.fromSource 0 (by decide), .job 0, .precedence 0 1 (by decide), .job 1,
        .precedence 1 2 (by decide), .job 2, .toSink 2 (by decide)], by walk_tac, by decide⟩
    · fin_cases j
      · exact ⟨[.fromSource 0 (by decide)], by walk_tac, by decide⟩
      · exact ⟨[.fromSource 0 (by decide), .job 0, .precedence 0 1 (by decide)], by walk_tac,
          by decide⟩
      · exact ⟨[.fromSource 0 (by decide), .job 0, .precedence 0 1 (by decide), .job 1,
          .precedence 1 2 (by decide)], by walk_tac, by decide⟩
    · fin_cases j
      · exact ⟨[.fromSource 0 (by decide), .job 0], by walk_tac, by decide⟩
      · exact ⟨[.fromSource 0 (by decide), .job 0, .precedence 0 1 (by decide), .job 1],
          by walk_tac, by decide⟩
      · exact ⟨[.fromSource 0 (by decide), .job 0, .precedence 0 1 (by decide), .job 1,
          .precedence 1 2 (by decide), .job 2], by walk_tac, by decide⟩
  have h := mem_paths_filterMap_job?_of_sum_eq_sink (isAcyclic_of_lt (by decide)) hτ hwalk
    (l := [.fromSource 0 (by decide), .job 0, .precedence 0 1 (by decide), .job 1,
      .precedence 1 2 (by decide), .job 2, .toSink 2 (by decide)]) (by walk_tac) (by decide)
  exact ⟨h.1, by decide, rfl, by decide, h.2.2.2.1⟩

/-! ### Empty table: the declared arc is the only certificate, with the empty witness -/

def τEmpty : SplitEvent Empty → ℕ := fun _ => 0

example : (∃ l, IsArcWalk (splitTail (⊥ : Digraph Empty)) (splitHead (⊥ : Digraph Empty))
      .source .sink l ∧
      (l.map (splitDuration (⊥ : Digraph Empty) fun x => x.elim)).sum = τEmpty .sink ∧
      l.filterMap SplitArc.job? = []) ∧
    (∀ l, IsArcWalk (splitTail (⊥ : Digraph Empty)) (splitHead (⊥ : Digraph Empty))
      .source .sink l →
      (l.map (splitDuration (⊥ : Digraph Empty) fun x => x.elim)).sum = τEmpty .sink →
      l = [.sourceSink]) ∧
    projectFinish (fun x : Empty => x.elim) (fun j => τEmpty (.input j)) = 0 := by
  have hG : (⊥ : Digraph Empty).IsAcyclic := fun v => v.elim
  have hτ : IsFeasibleSchedule (splitTail (⊥ : Digraph Empty)) (splitHead (⊥ : Digraph Empty))
      (splitDuration (⊥ : Digraph Empty) fun x => x.elim) τEmpty := by
    intro e
    cases e with
    | job j => exact j.elim
    | precedence i _ _ => exact i.elim
    | fromSource j _ => exact j.elim
    | toSink j _ => exact j.elim
    | sourceSink => exact le_refl _
  have hwalk : ∀ v, ∃ l, IsArcWalk (splitTail (⊥ : Digraph Empty))
      (splitHead (⊥ : Digraph Empty)) .source v l ∧
      (l.map (splitDuration (⊥ : Digraph Empty) fun x => x.elim)).sum = τEmpty v := by
    rintro (_ | _ | j | j)
    · exact ⟨[], walk_nil, rfl⟩
    · exact ⟨[.sourceSink], walk_singleton rfl rfl, rfl⟩
    · exact j.elim
    · exact j.elim
  refine ⟨(exists_isArcWalk_sum_eq_sink_filterMap_job?_eq_nil_iff hG hτ hwalk).mpr
    fun j => j.elim, fun l hl hdur => ?_, by simp [projectFinish]⟩
  have h := (mem_paths_filterMap_job?_of_sum_eq_sink hG hτ hwalk hl hdur).2.2.2.2
  refine h.mp ?_
  generalize l.filterMap SplitArc.job? = c
  cases c with
  | nil => rfl
  | cons x _ => exact x.elim

/-! ### All durations zero, `0 → 1`: the declared arc ties with the chain `[0, 1]` -/

def g01 : Digraph (Fin 2) where
  Adj i j := i = 0 ∧ j = 1

instance : DecidableRel g01.Adj := fun i j => inferInstanceAs (Decidable (i = 0 ∧ j = 1))

def τZero : SplitEvent (Fin 2) → ℕ := fun _ => 0

private theorem hτZero :
    IsFeasibleSchedule (splitTail g01) (splitHead g01) (splitDuration g01 ![0, 0]) τZero := by
  intro e
  cases e with
  | job j => fin_cases j <;> decide
  | precedence i j h => revert h; fin_cases i <;> fin_cases j <;> decide
  | fromSource j h => revert h; fin_cases j <;> decide
  | toSink j h => revert h; fin_cases j <;> decide
  | sourceSink => decide

private theorem hwalkZero : ∀ v, ∃ l, IsArcWalk (splitTail g01) (splitHead g01) .source v l ∧
    (l.map (splitDuration g01 ![0, 0])).sum = τZero v := by
  intro v
  rcases v with _ | _ | j | j
  · exact ⟨[], walk_nil, rfl⟩
  · exact ⟨[.sourceSink], walk_singleton rfl rfl, rfl⟩
  · fin_cases j
    · exact ⟨[.fromSource 0 (by decide)], by walk_tac, by decide⟩
    · exact ⟨[.fromSource 0 (by decide), .job 0, .precedence 0 1 (by decide)], by walk_tac,
        by decide⟩
  · fin_cases j
    · exact ⟨[.fromSource 0 (by decide), .job 0], by walk_tac, by decide⟩
    · exact ⟨[.fromSource 0 (by decide), .job 0, .precedence 0 1 (by decide), .job 1],
        by walk_tac, by decide⟩

example : (∃ l, IsArcWalk (splitTail g01) (splitHead g01) .source .sink l ∧
      (l.map (splitDuration g01 ![0, 0])).sum = τZero .sink ∧
      l.filterMap SplitArc.job? = []) ∧
    ([0, 1] : List (Fin 2)) ∈ g01.paths ∧
    (([0, 1] : List (Fin 2)).map ![0, 0]).sum =
      projectFinish ![0, 0] (fun j => τZero (.input j)) := by
  have hG : g01.IsAcyclic := isAcyclic_of_lt (by decide)
  have h := mem_paths_filterMap_job?_of_sum_eq_sink hG hτZero hwalkZero
    (l := [.fromSource 0 (by decide), .job 0, .precedence 0 1 (by decide), .job 1,
      .toSink 1 (by decide)]) (by walk_tac) (by decide)
  exact ⟨(exists_isArcWalk_sum_eq_sink_filterMap_job?_eq_nil_iff hG hτZero hwalkZero).mpr
    (by decide), h.1, h.2.2.2.1⟩

/-! ### Two disconnected jobs, durations `3, 5`: the witness is the single job `[1]` -/

def gDisc : Digraph (Fin 2) where
  Adj _ _ := False

instance : DecidableRel gDisc.Adj := fun _ _ => inferInstanceAs (Decidable False)

def τDisc : SplitEvent (Fin 2) → ℕ
  | .source => 0
  | .sink => 5
  | .input _ => 0
  | .output j => ![3, 5] j

example : ([1] : List (Fin 2)) ∈ gDisc.paths ∧ (∀ i, ¬ gDisc.Adj i 1) ∧ (∀ k, ¬ gDisc.Adj 1 k) ∧
    (([1] : List (Fin 2)).map ![3, 5]).sum = projectFinish ![3, 5] (fun j => τDisc (.input j)) ∧
    projectFinish ![3, 5] (fun j => τDisc (.input j)) = 5 ∧
    ([.fromSource 0 (fun _ h => h), .job 0, .toSink 0 (fun _ h => h)].map
      (splitDuration gDisc ![3, 5])).sum ≠ τDisc .sink ∧
    ¬ ∃ l, IsArcWalk (splitTail gDisc) (splitHead gDisc) .source .sink l ∧
      (l.map (splitDuration gDisc ![3, 5])).sum = τDisc .sink ∧
      l.filterMap SplitArc.job? = [] := by
  have hG : gDisc.IsAcyclic := isAcyclic_of_lt (by decide)
  have hτ : IsFeasibleSchedule (splitTail gDisc) (splitHead gDisc) (splitDuration gDisc ![3, 5])
      τDisc := by
    intro e
    cases e with
    | job j => fin_cases j <;> decide
    | precedence i j h => exact h.elim
    | fromSource j h => revert h; fin_cases j <;> decide
    | toSink j h => revert h; fin_cases j <;> decide
    | sourceSink => decide
  have hwalk : ∀ v, ∃ l, IsArcWalk (splitTail gDisc) (splitHead gDisc) .source v l ∧
      (l.map (splitDuration gDisc ![3, 5])).sum = τDisc v := by
    intro v
    rcases v with _ | _ | j | j
    · exact ⟨[], walk_nil, rfl⟩
    · exact ⟨[.fromSource 1 (fun _ h => h), .job 1, .toSink 1 (fun _ h => h)], by walk_tac,
        by decide⟩
    · exact ⟨[.fromSource j (fun _ h => h)], by walk_tac, rfl⟩
    · fin_cases j
      · exact ⟨[.fromSource 0 (fun _ h => h), .job 0], by walk_tac, by decide⟩
      · exact ⟨[.fromSource 1 (fun _ h => h), .job 1], by walk_tac, by decide⟩
  have h := mem_paths_filterMap_job?_of_sum_eq_sink hG hτ hwalk
    (l := [.fromSource 1 (fun _ h => h), .job 1, .toSink 1 (fun _ h => h)]) (by walk_tac)
    (by decide)
  refine ⟨h.1, h.2.1 1 rfl, h.2.2.1 1 rfl, h.2.2.2.1, by decide, by decide, fun hex => ?_⟩
  exact absurd ((exists_isArcWalk_sum_eq_sink_filterMap_job?_eq_nil_iff hG hτ hwalk).mp hex 0)
    (by decide)

end CSLibExtTest.Scheduling.ProjectNetwork.CriticalPath

#print axioms Cslib.Scheduling.ProjectNetwork.mem_paths_filterMap_job?_of_sum_eq_sink
#print axioms Cslib.Scheduling.ProjectNetwork.exists_isArcWalk_sum_eq_sink_filterMap_job?_eq_nil_iff
