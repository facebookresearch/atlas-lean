/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Scheduling.ProjectNetwork.EarliestSchedule
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Earliest-schedule checks

Concrete consumers of `CSLibExt.Scheduling.ProjectNetwork.EarliestSchedule`: two start jobs
joining before a final job, a zero-duration milestone, the empty table, and a cyclic table on
which the project-finish equation needs acyclicity. Elaboration checks, not results.
-/

namespace CSLibExtTest.Scheduling.ProjectNetwork.EarliestSchedule

open Cslib.Scheduling.ProjectNetwork MathlibExt.Combinatorics.Graph.ArcNetwork

macro "walk_tac" : tactic =>
  `(tactic| (repeat (first | exact walk_nil | refine walk_cons_mk rfl ?_)))

/-- Two start jobs `0`, `1` join before job `2`; durations `3, 5, 2`. -/
def gJoin : Digraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)

instance : DecidableRel gJoin.Adj := fun i j =>
  inferInstanceAs (Decidable ((i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)))

/-- Earliest event dates of the join table: starts `0, 0, 5`, finishes `3, 5, 7`, sink `7`. -/
def τJoin : SplitEvent (Fin 3) → ℕ
  | .source => 0
  | .sink => 7
  | .input j => ![0, 0, 5] j
  | .output j => ![3, 5, 7] j

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

/-- Two starts join before the final job: the earliest schedule `0, 0, 5` is the least feasible
schedule, its project finish `7` is the sink date, `7` is the least project finish, and the
feasible schedule `0, 1, 6` (finish `8`) is not least. -/
example : IsLeast {s : Fin 3 → ℕ | IsPrecedenceFeasible gJoin ![3, 5, 2] s} ![0, 0, 5] ∧
    projectFinish ![3, 5, 2] (fun j => τJoin (.input j)) = τJoin .sink ∧
    IsLeast (projectFinish ![3, 5, 2] ''
      {s : Fin 3 → ℕ | IsPrecedenceFeasible gJoin ![3, 5, 2] s}) 7 ∧
    ¬ IsLeast {s : Fin 3 → ℕ | IsPrecedenceFeasible gJoin ![3, 5, 2] s} ![0, 1, 6] := by
  have hacyc : gJoin.IsAcyclic := by
    have hlt : ∀ a b : Fin 3, gJoin.Adj a b → a < b := by decide
    intro v h
    have key : ∀ a b, Relation.TransGen gJoin.Adj a b → a < b := by
      intro a b hab
      induction hab with
      | single h => exact hlt _ _ h
      | tail _ h ih => exact lt_trans ih (hlt _ _ h)
    exact lt_irrefl v (key v v h)
  have hstart : (fun j => τJoin (.input j)) = ![0, 0, 5] := by funext j; fin_cases j <;> rfl
  have h2 := isLeast_input hτJoin hwalkJoin
  have h3 := projectFinish_input_eq_sink hacyc hτJoin hwalkJoin
  have h4 := isLeast_projectFinish_input hτJoin hwalkJoin
  rw [h3] at h4
  refine ⟨hstart ▸ h2, h3, h4, fun h => ?_⟩
  have := h.2 h2.1 1
  revert this; decide

/-- Zero-duration milestone on the chain `0 → 1 → 2`, durations `4, 0, 3`: the milestone starts
and finishes at tick `4`. -/
def gChain : Digraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

instance : DecidableRel gChain.Adj := fun i j =>
  inferInstanceAs (Decidable ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)))

def τChain : SplitEvent (Fin 3) → ℕ
  | .source => 0
  | .sink => 7
  | .input j => ![0, 4, 4] j
  | .output j => ![4, 4, 7] j

example : τChain (.output 1) = τChain (.input 1) + (![4, 0, 3] : Fin 3 → ℕ) 1 ∧
    τChain (.input 1) = 4 := by
  refine ⟨output_eq_input_add (G := gChain) ?_ ?_ 1, rfl⟩
  · intro e
    cases e with
    | job j => fin_cases j <;> decide
    | precedence i j h => revert h; fin_cases i <;> fin_cases j <;> decide
    | fromSource j h => revert h; fin_cases j <;> decide
    | toSink j h => revert h; fin_cases j <;> decide
    | sourceSink => decide
  · intro v
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

/-- Empty project: every earliest-date schedule of the empty table has sink date `0`. -/
example (τ : SplitEvent Empty → ℕ)
    (hτ : IsFeasibleSchedule (splitTail (⊥ : Digraph Empty)) (splitHead (⊥ : Digraph Empty))
      (splitDuration (⊥ : Digraph Empty) fun x => x.elim) τ)
    (hwalk : ∀ v, ∃ l, IsArcWalk (splitTail (⊥ : Digraph Empty)) (splitHead (⊥ : Digraph Empty))
      .source v l ∧ (l.map (splitDuration (⊥ : Digraph Empty) fun x => x.elim)).sum = τ v) :
    τ .sink = 0 := by
  have h := projectFinish_input_eq_sink (fun v => v.elim) hτ hwalk
  simp [projectFinish] at h
  exact h.symm

/-- Acyclicity is needed for the project-finish equation: behind start job `0` (duration `5`)
the zero-duration cycle `1 → 2 → 1` has no finish job, so the sink date is `0` while the
earliest job finishes are `5`. -/
def gCyc : Digraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)

instance : DecidableRel gCyc.Adj := fun i j =>
  inferInstanceAs (Decidable ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)))

def τCyc : SplitEvent (Fin 3) → ℕ
  | .source => 0
  | .sink => 0
  | .input j => ![0, 5, 5] j
  | .output _ => 5

example : ¬ gCyc.IsAcyclic ∧
    IsFeasibleSchedule (splitTail gCyc) (splitHead gCyc) (splitDuration gCyc ![5, 0, 0]) τCyc ∧
    (∀ v, ∃ l, IsArcWalk (splitTail gCyc) (splitHead gCyc) .source v l ∧
      (l.map (splitDuration gCyc ![5, 0, 0])).sum = τCyc v) ∧
    projectFinish ![5, 0, 0] (fun j => τCyc (.input j)) ≠ τCyc .sink := by
  refine ⟨fun h => h 1 ((Relation.TransGen.single (show gCyc.Adj 1 2 by decide)).tail
    (show gCyc.Adj 2 1 by decide)), ?_, ?_, by decide⟩
  · intro e
    cases e with
    | job j => fin_cases j <;> decide
    | precedence i j h => revert h; fin_cases i <;> fin_cases j <;> decide
    | fromSource j h => revert h; fin_cases j <;> decide
    | toSink j h => revert h; fin_cases j <;> decide
    | sourceSink => decide
  · intro v
    rcases v with _ | _ | j | j
    · exact ⟨[], walk_nil, rfl⟩
    · exact ⟨[.sourceSink], by walk_tac, rfl⟩
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

end CSLibExtTest.Scheduling.ProjectNetwork.EarliestSchedule

#print axioms Cslib.Scheduling.ProjectNetwork.output_eq_input_add
#print axioms Cslib.Scheduling.ProjectNetwork.isLeast_input
#print axioms Cslib.Scheduling.ProjectNetwork.projectFinish_input_eq_sink
#print axioms Cslib.Scheduling.ProjectNetwork.isLeast_projectFinish_input
