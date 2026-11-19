/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE TOTAL COMPLETION TIME WITH RELEASE TIMES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS4] SEQUENCING TO MINIMIZE
WEIGHTED COMPLETION TIME (comment: with individual task release times instead of the partial
order, NP-complete in the strong sense even if all task weights are 1);
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X, Theorem 4(a) (KNAPSACK reduces to `1|rⱼ|∑ Cⱼ`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Defs
public import WantedExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalCompletionTimeWithReleaseTimes

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-!
# SEQUENCING TO MINIMIZE TOTAL COMPLETION TIME WITH RELEASE TIMES is NP-complete

INSTANCE: a set `T` of tasks, for each task `t ∈ T` a length `l(t) ∈ ℤ⁺` and a release time
`r(t) ∈ ℤ₀⁺`, and a positive integer `K`. QUESTION: is there a one-processor schedule `σ` for
`T` with `σ(t) ≥ r(t)` for all `t ∈ T` such that the sum, over all `t ∈ T`, of
`σ(t) + l(t)` is `K` or less?

This is SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME ([SS4]) with individual release times
in place of the partial order and every task weight `w(t) = 1` (`1|rⱼ|∑ Cⱼ`), so the weights
are not part of the instance. A one-processor schedule (Garey and Johnson, [SS1]) is a
one-to-one function `σ : T → ℤ₀⁺` with `σ(t) > σ(t')` implying `σ(t) ≥ σ(t') + l(t')`; the
predicate `IsOneProcessorSchedule` is reused from `SequencingToMinimizeWeightedTardinessWanted`.
The tasks are `Fin n`, one per listed pair `(l(t), r(t))`. Binary encoding of all numbers (the
problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the tasks, task `t` being the `t`-th pair `(l(t), r(t))` of length and release
time, and the bound `K`. -/
abbrev TotalCompletionTimeWithReleaseTimesInstance := List (ℕ × ℕ) × ℕ

/-- The tasks of the instance, `Fin n` for `n` listed pairs. -/
abbrev Task (i : TotalCompletionTimeWithReleaseTimesInstance) : Type := Fin i.1.length

/-- The length `l(t)` of task `t`. -/
def taskLength (i : TotalCompletionTimeWithReleaseTimesInstance) (t : Task i) : ℕ :=
  (i.1.get t).1

/-- The release time `r(t)` of task `t`. -/
def releaseTime (i : TotalCompletionTimeWithReleaseTimesInstance) (t : Task i) : ℕ :=
  (i.1.get t).2

/-- Well-formedness of an instance: every task length is positive, and `K` is positive. -/
def WellFormed (i : TotalCompletionTimeWithReleaseTimesInstance) : Prop :=
  (∀ x ∈ i.1, 0 < x.1) ∧ 0 < i.2

/-- Some one-processor schedule starts every task no earlier than its release time and has
total completion time `∑ₜ (σ(t) + l(t))` at most `K`. -/
def TotalCompletionTimeWithReleaseTimesFeasible
    (i : TotalCompletionTimeWithReleaseTimesInstance) : Prop :=
  ∃ σ : Task i → ℕ, IsOneProcessorSchedule (taskLength i) σ ∧
    (∀ t, releaseTime i t ≤ σ t) ∧
    ∑ t, (σ t + taskLength i t) ≤ i.2

open Classical in
/-- SEQUENCING TO MINIMIZE TOTAL COMPLETION TIME WITH RELEASE TIMES as a decision problem over
bitstrings. -/
noncomputable def totalCompletionTimeWithReleaseTimesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TotalCompletionTimeWithReleaseTimesInstance) x with
  | some i => decide (WellFormed i ∧ TotalCompletionTimeWithReleaseTimesFeasible i)
  | none => false

/-- **SEQUENCING TO MINIMIZE TOTAL COMPLETION TIME WITH RELEASE TIMES is NP-complete.**
Source: Garey and Johnson (1979), [SS4]; Lenstra, Rinnooy Kan, and Brucker (1977),
Theorem 4(a). -/
public theorem_wanted totalCompletionTimeWithReleaseTimes_npComplete :
    totalCompletionTimeWithReleaseTimesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L totalCompletionTimeWithReleaseTimesDec

end MetaMathlibExt.Complexity.NPComplete.TotalCompletionTimeWithReleaseTimes
