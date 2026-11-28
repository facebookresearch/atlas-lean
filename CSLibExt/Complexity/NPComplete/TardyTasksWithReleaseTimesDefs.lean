/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE TARDY TASKS WITH RELEASE TIMES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS2] SEQUENCING TO MINIMIZE
TARDY TASKS, p. 236, comment (with `<` empty, NP-complete "for arbitrary release times (see
previous problem)", i.e. [SS1] SEQUENCING WITH RELEASE TIMES AND DEADLINES, NP-complete in the
strong sense);
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X, Theorem 4(f) (KNAPSACK reduces to
`n|1|rⱼ ≥ 0, wⱼ = 1|∑ wⱼUⱼ`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TardyTasksWithReleaseTimes

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-- An instance: the tasks, task `t` being the `t`-th triple `(l(t), r(t), d(t))` of length,
release time and deadline, and the bound `K`. -/
abbrev TardyTasksWithReleaseTimesInstance := List (ℕ × ℕ × ℕ) × ℕ

/-- The tasks of the instance, `Fin n` for `n` listed triples. -/
abbrev Task (i : TardyTasksWithReleaseTimesInstance) : Type := Fin i.1.length

/-- The length `l(t)` of task `t`. -/
def taskLength (i : TardyTasksWithReleaseTimesInstance) (t : Task i) : ℕ :=
  (i.1.get t).1

/-- The release time `r(t)` of task `t`. -/
def releaseTime (i : TardyTasksWithReleaseTimesInstance) (t : Task i) : ℕ :=
  (i.1.get t).2.1

/-- The deadline `d(t)` of task `t`. -/
def deadline (i : TardyTasksWithReleaseTimesInstance) (t : Task i) : ℕ :=
  (i.1.get t).2.2

/-- Well-formedness of an instance: every length and deadline is positive, and
`0 < K ≤ |T|`. -/
def WellFormed (i : TardyTasksWithReleaseTimesInstance) : Prop :=
  (∀ x ∈ i.1, 0 < x.1 ∧ 0 < x.2.2) ∧ 0 < i.2 ∧ i.2 ≤ i.1.length

/-- Some one-processor schedule starts every task no earlier than its release time and has at
most `K` tardy tasks, those with `σ(t) + l(t) > d(t)`. -/
def TardyTasksWithReleaseTimesFeasible (i : TardyTasksWithReleaseTimesInstance) : Prop :=
  ∃ σ : Task i → ℕ, IsOneProcessorSchedule (taskLength i) σ ∧
    (∀ t, releaseTime i t ≤ σ t) ∧
    (Finset.univ.filter fun t => deadline i t < σ t + taskLength i t).card ≤ i.2

open Classical in
/-- SEQUENCING TO MINIMIZE TARDY TASKS WITH RELEASE TIMES as a decision problem over
bitstrings. -/
noncomputable def tardyTasksWithReleaseTimesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TardyTasksWithReleaseTimesInstance) x with
  | some i => decide (WellFormed i ∧ TardyTasksWithReleaseTimesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TardyTasksWithReleaseTimes
