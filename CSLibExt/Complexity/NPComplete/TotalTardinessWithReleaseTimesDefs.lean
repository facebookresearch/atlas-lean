/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE TOTAL TARDINESS WITH RELEASE TIMES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS5] SEQUENCING TO MINIMIZE
WEIGHTED TARDINESS, p. 237, comment ("If release times are added instead, the problem is
NP-complete in the strong sense for equal task weights (see SEQUENCING WITH RELEASE TIMES AND
DEADLINES)");
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X, Theorems 4(a) and 1(j) (`n|1|rⱼ ≥ 0, wⱼ = 1|∑ wⱼCⱼ`
reduces to `n|1|rⱼ ≥ 0, wⱼ = 1|∑ wⱼTⱼ`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Defs
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalTardinessWithReleaseTimes

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-- An instance: the tasks, task `t` being the `t`-th triple `(l(t), r(t), d(t))` of length,
release time and deadline, and the bound `K`. -/
abbrev TotalTardinessWithReleaseTimesInstance := List (ℕ × ℕ × ℕ) × ℕ

/-- The tasks of the instance, `Fin n` for `n` listed triples. -/
abbrev Task (i : TotalTardinessWithReleaseTimesInstance) : Type := Fin i.1.length

/-- The length `l(t)` of task `t`. -/
def taskLength (i : TotalTardinessWithReleaseTimesInstance) (t : Task i) : ℕ :=
  (i.1.get t).1

/-- The release time `r(t)` of task `t`. -/
def releaseTime (i : TotalTardinessWithReleaseTimesInstance) (t : Task i) : ℕ :=
  (i.1.get t).2.1

/-- The deadline `d(t)` of task `t`. -/
def deadline (i : TotalTardinessWithReleaseTimesInstance) (t : Task i) : ℕ :=
  (i.1.get t).2.2

/-- Well-formedness of an instance: every length and deadline is positive, and `K` is
positive. -/
def WellFormed (i : TotalTardinessWithReleaseTimesInstance) : Prop :=
  (∀ x ∈ i.1, 0 < x.1 ∧ 0 < x.2.2) ∧ 0 < i.2

/-- Some one-processor schedule starts every task no earlier than its release time and has
total tardiness at most `K`: the sum, over the tasks with `σ(t) + l(t) > d(t)`, of
`σ(t) + l(t) - d(t)` is at most `K`. -/
def TotalTardinessWithReleaseTimesFeasible (i : TotalTardinessWithReleaseTimesInstance) :
    Prop :=
  ∃ σ : Task i → ℕ, IsOneProcessorSchedule (taskLength i) σ ∧
    (∀ t, releaseTime i t ≤ σ t) ∧
    ∑ t ∈ Finset.univ.filter (fun t => deadline i t < σ t + taskLength i t),
      (σ t + taskLength i t - deadline i t) ≤ i.2

open Classical in
/-- SEQUENCING TO MINIMIZE TOTAL TARDINESS WITH RELEASE TIMES as a decision problem over
bitstrings. -/
noncomputable def totalTardinessWithReleaseTimesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TotalTardinessWithReleaseTimesInstance) x with
  | some i => decide (WellFormed i ∧ TotalTardinessWithReleaseTimesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TotalTardinessWithReleaseTimes
