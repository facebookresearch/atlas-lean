/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING WITH RELEASE TIMES TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), problem [SS4] MINIMUM SEQUENCING WITH RELEASE TIMES;
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X, Theorem 4(a) (`1|rⱼ|∑ Cⱼ` is NP-hard).
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

namespace MetaMathlibExt.Complexity.NPComplete.WeightedCompletionTimeWithReleaseTimes

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-!
# SEQUENCING WITH RELEASE TIMES TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete

INSTANCE: a set `T` of tasks, for each task `t ∈ T` a release time `r(t)`, a length
`l(t) ∈ ℤ⁺` and a weight `w(t) ∈ ℤ⁺`, and a positive integer `K`. QUESTION: is there a
one-processor schedule `f` for `T` that obeys the release times (`f(t) ≥ r(t)` for every task)
such that the weighted sum of completion times `∑_{t ∈ T} w(t) (f(t) + l(t))` is at most `K`?

This is the decision version, with bound `K`, of Crescenzi and Kann's [SS4] MINIMUM SEQUENCING
WITH RELEASE TIMES (`1|rⱼ|∑ wⱼCⱼ`). Crescenzi and Kann define the schedule as a function
`f : T → ℕ` such that at every time `u` the set `S(u)` of tasks `t` with `f(t) ≤ u < f(t) + l(t)`
has one element; read literally ("`|S(u)| = 1` for all `u ≥ 0`") no schedule would exist after
the last task finishes, so this is the usual one-task-at-a-time condition `|S(u)| ≤ 1`, which for
positive lengths is Garey and Johnson's one-processor schedule ([SS1]: `σ` one-to-one, and
`σ(t) > σ(t')` implies `σ(t) ≥ σ(t') + l(t')`), the predicate `IsOneProcessorSchedule` reused
from `SequencingToMinimizeWeightedTardinessWanted`. Crescenzi and Kann write `r(t) ∈ ℤ⁺`;
release times here are in `ℤ₀⁺`, as in Lenstra, Rinnooy Kan and Brucker and in
`TotalCompletionTimeWithReleaseTimesWanted` (adding one to every release time maps the
instances with release times `0` into those with positive release times, raising every cost by
`∑ w(t)`). The case `w(t) = 1` for all `t` is `1|rⱼ|∑ Cⱼ`
(`TotalCompletionTimeWithReleaseTimesWanted`), NP-hard by Lenstra, Rinnooy Kan and Brucker
(1977), Theorem 4(a); its instances are instances of this problem with all weights `1` and the
same answer, so this problem is NP-hard too. It is in NP: in a schedule of cost at most `K` every
start time is below `K` (weights are positive), so the start times form a certificate of
polynomial size.

The tasks are `Fin n`, one per listed triple `(l(t), r(t), w(t))`. Binary encoding of all
numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SEQUENCING WITH RELEASE TIMES TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete.**
Source: Crescenzi and Kann (2000), [SS4]; Lenstra, Rinnooy Kan, and Brucker (1977),
Theorem 4(a). -/
public theorem_wanted weightedCompletionTimeWithReleaseTimes_npComplete :
    weightedCompletionTimeWithReleaseTimesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedCompletionTimeWithReleaseTimesDec

end MetaMathlibExt.Complexity.NPComplete.WeightedCompletionTimeWithReleaseTimes
