/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS13] SCHEDULING TO MINIMIZE
WEIGHTED COMPLETION TIME;
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTime

/-- An instance: the number of processors `m`, one pair `(l(t), w(t))` (length, weight) per task
`t`, and the bound `K`. -/
abbrev SchedulingToMinimizeWeightedCompletionTimeInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The tasks of the instance, `Fin n` for `n` listed pairs. -/
abbrev Task (i : SchedulingToMinimizeWeightedCompletionTimeInstance) : Type :=
  Fin i.2.1.length

/-- The length `l(t)` of task `t`. -/
def taskLength (i : SchedulingToMinimizeWeightedCompletionTimeInstance) (t : Task i) : ℕ :=
  (i.2.1.get t).1

/-- The weight `w(t)` of task `t`. -/
def weight (i : SchedulingToMinimizeWeightedCompletionTimeInstance) (t : Task i) : ℕ :=
  (i.2.1.get t).2

/-- The tasks running at time `u` under `σ`: those with `σ(t) ≤ u < σ(t) + l(t)`. -/
def running (i : SchedulingToMinimizeWeightedCompletionTimeInstance) (σ : Task i → ℕ) (u : ℕ) :
    Finset (Task i) :=
  Finset.univ.filter fun t => σ t ≤ u ∧ u < σ t + taskLength i t

/-- The weighted completion time `∑ t, (σ(t) + l(t)) · w(t)` of `σ`. -/
def weightedCompletionTime (i : SchedulingToMinimizeWeightedCompletionTimeInstance)
    (σ : Task i → ℕ) : ℕ :=
  ∑ t, (σ t + taskLength i t) * weight i t

/-- Well-formedness of an instance: `0 < m`, every length and every weight is positive, and
`0 < K`. -/
def WellFormed (i : SchedulingToMinimizeWeightedCompletionTimeInstance) : Prop :=
  0 < i.1 ∧ (∀ p ∈ i.2.1, 0 < p.1 ∧ 0 < p.2) ∧ 0 < i.2.2

/-- Some `m`-processor schedule (at every time `u` at most `m` tasks run) has weighted
completion time at most `K`. -/
def SchedulingToMinimizeWeightedCompletionTimeFeasible
    (i : SchedulingToMinimizeWeightedCompletionTimeInstance) : Prop :=
  ∃ σ : Task i → ℕ, (∀ u, (running i σ u).card ≤ i.1) ∧ weightedCompletionTime i σ ≤ i.2.2

open Classical in
/-- SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME as a decision problem over bitstrings. -/
noncomputable def schedulingToMinimizeWeightedCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SchedulingToMinimizeWeightedCompletionTimeInstance) x with
  | some i => decide (WellFormed i ∧ SchedulingToMinimizeWeightedCompletionTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTime
