/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING WITH RELEASE TIMES TO MINIMIZE WEIGHTED COMPLETION TIME: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), problem MINIMUM SEQUENCING WITH RELEASE TIMES;
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X, Theorem 4(a) (`1|rⱼ|∑ Cⱼ` is NP-hard).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Defs
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedCompletionTimeWithReleaseTimes

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-- An instance: the tasks, task `t` being the `t`-th triple `(l(t), r(t), w(t))` of length,
release time and weight, and the bound `K`. -/
abbrev WeightedCompletionTimeWithReleaseTimesInstance := List (ℕ × ℕ × ℕ) × ℕ

/-- The tasks of the instance, `Fin n` for `n` listed triples. -/
abbrev Task (i : WeightedCompletionTimeWithReleaseTimesInstance) : Type := Fin i.1.length

/-- The length `l(t)` of task `t`. -/
def taskLength (i : WeightedCompletionTimeWithReleaseTimesInstance) (t : Task i) : ℕ :=
  (i.1.get t).1

/-- The release time `r(t)` of task `t`. -/
def releaseTime (i : WeightedCompletionTimeWithReleaseTimesInstance) (t : Task i) : ℕ :=
  (i.1.get t).2.1

/-- The weight `w(t)` of task `t`. -/
def weight (i : WeightedCompletionTimeWithReleaseTimesInstance) (t : Task i) : ℕ :=
  (i.1.get t).2.2

/-- Well-formedness of an instance: every task length and weight is positive, and `K` is
positive. -/
def WellFormed (i : WeightedCompletionTimeWithReleaseTimesInstance) : Prop :=
  (∀ x ∈ i.1, 0 < x.1 ∧ 0 < x.2.2) ∧ 0 < i.2

/-- Some one-processor schedule starts every task no earlier than its release time and has
weighted completion time `∑ₜ w(t) (σ(t) + l(t))` at most `K`. -/
def WeightedCompletionTimeWithReleaseTimesFeasible
    (i : WeightedCompletionTimeWithReleaseTimesInstance) : Prop :=
  ∃ σ : Task i → ℕ, IsOneProcessorSchedule (taskLength i) σ ∧
    (∀ t, releaseTime i t ≤ σ t) ∧
    ∑ t, weight i t * (σ t + taskLength i t) ≤ i.2

open Classical in
/-- SEQUENCING WITH RELEASE TIMES TO MINIMIZE WEIGHTED COMPLETION TIME as a decision problem
over bitstrings. -/
noncomputable def weightedCompletionTimeWithReleaseTimesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedCompletionTimeWithReleaseTimesInstance) x with
  | some i => decide (WellFormed i ∧ WeightedCompletionTimeWithReleaseTimesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WeightedCompletionTimeWithReleaseTimes
