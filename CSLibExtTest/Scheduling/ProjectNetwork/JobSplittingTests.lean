/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Scheduling.ProjectNetwork.JobSplitting
public import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Job-splitting checks

Concrete consumers of `CSLibExt.Scheduling.ProjectNetwork.JobSplitting`: the four-job table
`0 → 2, 1 → 2, 1 → 3` with durations `(3, 5, 2, 4)`, the empty table, a zero-duration
milestone, a cyclic table, and infeasible starts. Elaboration checks, not results.
-/

namespace CSLibExtTest.Scheduling.ProjectNetwork

open Cslib.Scheduling.ProjectNetwork MathlibExt.Combinatorics.Graph.ArcNetwork

/-- The four-job precedence table `0 → 2, 1 → 2, 1 → 3`. -/
private def g4 : Digraph (Fin 4) where
  Adj i j := (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3)

private theorem g4_adj {i j : Fin 4} :
    g4.Adj i j = ((i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3)) := rfl

private theorem g4_lt {a b : Fin 4} (h : Relation.TransGen g4.Adj a b) : a < b := by
  induction h with
  | single h =>
    simp only [g4_adj] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  | tail _ h ih =>
    simp only [g4_adj] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

/-- The four-job table is acyclic, `(0, 0, 5, 5)` is feasible with project finish `9`, and
`[1, 3]` is a critical chain from a start job to a finish job. -/
private theorem w1 : g4.IsAcyclic ∧ IsPrecedenceFeasible g4 ![3, 5, 2, 4] ![0, 0, 5, 5] ∧
    projectFinish ![3, 5, 2, 4] ![0, 0, 5, 5] = 9 ∧
    ([1, 3] : List (Fin 4)).IsChain g4.Adj ∧ (([1, 3] : List (Fin 4)).map ![3, 5, 2, 4]).sum = 9 ∧
    (∀ i, ¬ g4.Adj i 1) ∧ (∀ k, ¬ g4.Adj 3 k) := by
  refine ⟨fun v h => lt_irrefl v (g4_lt h), ?_, by decide, by simp [List.isChain_cons, g4_adj],
    by decide, ?_, ?_⟩
  · intro i j h
    simp only [g4_adj] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  all_goals intro x h; simp only [g4_adj] at h; omega

/-- Through the network: the critical chain's walk has duration `9`, and the owner earliest
schedule for the split network has sink date `9`, the project finish. -/
example : ∃ τ : SplitEvent (Fin 4) → ℕ,
    IsFeasibleSchedule (splitTail g4) (splitHead g4) (splitDuration g4 ![3, 5, 2, 4]) τ ∧
      τ .source = 0 ∧ τ .sink = 9 := by
  obtain ⟨hg, hfeas, hfin, hc, hsum, h1, h3⟩ := w1
  obtain ⟨l, hl, hjobs⟩ := exists_isArcWalk_filterMap_job?_eq hc (by simpa using h1)
    (by simpa using h3)
  have hwalk : (l.map (splitDuration g4 ![3, 5, 2, 4])).sum = 9 := by
    rw [sum_map_splitDuration, hjobs, hsum]
  obtain ⟨τ, hτ, hτ0, hτv⟩ := exists_isFeasibleSchedule_eq_sum (splitDuration g4 ![3, 5, 2, 4])
    (eq_nil_of_isArcWalk_split_self hg)
    (fun v => (exists_isArcWalk_source_sink hg v).1)
  obtain ⟨l', hl', hsum'⟩ := hτv .sink
  have hle : τ .sink ≤ 9 := by
    have h := (isFeasibleSchedule_embedSchedule hfeas).add_sum_map_le hl'
    rw [hsum'] at h
    simpa [embedSchedule, hfin] using h
  have hge : 9 ≤ τ .sink := by
    have h := hτ.add_sum_map_le hl
    rw [hτ0, hwalk] at h
    simpa using h
  exact ⟨τ, hτ, hτ0, le_antisymm hle hge⟩

/-- The transported lower bound on the four-job table: the critical chain meets the finish. -/
example : (([1, 3] : List (Fin 4)).map ![3, 5, 2, 4]).sum
    ≤ projectFinish ![3, 5, 2, 4] ![0, 0, 5, 5] :=
  sum_map_le_projectFinish w1.2.1 w1.2.2.2.1

/-- Empty table: finish `0`, and the declared arc is the only source-to-sink walk. -/
example : projectFinish (fun x : Empty => x.elim) (fun x : Empty => x.elim) = 0 ∧
    ∀ l, IsArcWalk (splitTail (⊥ : Digraph Empty)) (splitHead (⊥ : Digraph Empty)) .source .sink
      l ↔ l = [.sourceSink] := by
  refine ⟨by simp [projectFinish], fun l => ⟨fun hl => ?_, fun hl => ?_⟩⟩
  · have h := (isChain_filterMap_job?_of_isArcWalk hl).2.2.2
    exact h.mp (List.eq_nil_of_subset_nil fun x _ => x.elim)
  · subst hl
    exact ⟨by simp, by simp [splitTail], by simp, by simp [splitHead]⟩

/-- Zero-duration milestone: the chain `0 → 1 → 2` with durations `4, 0, 3` and starts
`0, 4, 4` is feasible with project finish `7`. -/
def g3 : Digraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

private theorem g3_adj {i j : Fin 3} :
    g3.Adj i j = ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)) := rfl

example : IsPrecedenceFeasible g3 ![4, 0, 3] ![0, 4, 4] ∧
    projectFinish ![4, 0, 3] ![0, 4, 4] = 7 ∧
    ([0, 1, 2] : List (Fin 3)).IsChain g3.Adj ∧
    (([0, 1, 2] : List (Fin 3)).map ![4, 0, 3]).sum = 7 := by
  refine ⟨?_, by decide, by simp [List.isChain_cons, g3_adj], by decide⟩
  intro i j h
  simp only [g3_adj] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- The cyclic two-job table is not acyclic, and its split network has the nonempty closed
walk `input 0 → output 0 → input 1 → output 1 → input 0`: the closed-walk discharge needs
acyclicity. -/
def g2 : Digraph (Fin 2) where
  Adj i j := i ≠ j

private theorem g2_adj {i j : Fin 2} : g2.Adj i j = (i ≠ j) := rfl

example : ¬ g2.IsAcyclic ∧
    IsArcWalk (splitTail g2) (splitHead g2) (.input 0) (.input 0)
      [.job 0, .precedence 0 1 (by simp [g2_adj]), .job 1, .precedence 1 0 (by simp [g2_adj])] := by
  refine ⟨fun h => h 0 ?_, ?_⟩
  · exact Relation.TransGen.tail (Relation.TransGen.single (show g2.Adj 0 1 by simp [g2_adj])) (show g2.Adj 1 0 by simp [g2_adj])
  · refine ⟨by simp, by simp [splitTail], ?_, by simp [splitHead]⟩
    simp [List.IsChain, splitTail, splitHead]

/-- With infeasible starts, the embedded schedule is not feasible: the embedding needs its
precedence premise. -/
def g01 : Digraph (Fin 2) where
  Adj i j := i = 0 ∧ j = 1

private theorem g01_adj {i j : Fin 2} : g01.Adj i j = (i = 0 ∧ j = 1) := rfl

example : ¬ IsFeasibleSchedule (splitTail g01) (splitHead g01)
    (splitDuration g01 ![1, 1]) (embedSchedule ![1, 1] ![0, 0]) := fun h => by
  have := h (.precedence 0 1 (by simp [g01_adj]))
  simp [splitTail, splitHead, embedSchedule] at this

end CSLibExtTest.Scheduling.ProjectNetwork

#print axioms Cslib.Scheduling.ProjectNetwork.isFeasibleSchedule_embedSchedule
#print axioms Cslib.Scheduling.ProjectNetwork.isPrecedenceFeasible_input
#print axioms Cslib.Scheduling.ProjectNetwork.projectFinish_input_le_sink
#print axioms Cslib.Scheduling.ProjectNetwork.sum_map_splitDuration
#print axioms Cslib.Scheduling.ProjectNetwork.isChain_filterMap_job?_of_isArcWalk
#print axioms Cslib.Scheduling.ProjectNetwork.exists_isArcWalk_filterMap_job?_eq
#print axioms Cslib.Scheduling.ProjectNetwork.sum_map_le_projectFinish
#print axioms Cslib.Scheduling.ProjectNetwork.exists_isArcWalk_source_sink
#print axioms Cslib.Scheduling.ProjectNetwork.eq_nil_of_isArcWalk_split_self
#print axioms Cslib.Scheduling.ProjectNetwork.finite_splitArc
