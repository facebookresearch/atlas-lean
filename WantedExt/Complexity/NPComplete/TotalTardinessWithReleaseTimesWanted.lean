/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE TOTAL TARDINESS WITH RELEASE TIMES is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Defs
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalTardinessWithReleaseTimes

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-!
# SEQUENCING TO MINIMIZE TOTAL TARDINESS WITH RELEASE TIMES is NP-complete

INSTANCE: a set `T` of tasks, for each task `t ∈ T` a length `l(t) ∈ ℤ⁺`, a release time
`r(t) ∈ ℤ₀⁺` and a deadline `d(t) ∈ ℤ⁺`, and a positive integer `K`. QUESTION: is there a
one-processor schedule `σ` for `T` with `σ(t) ≥ r(t)` for all `t ∈ T` such that the sum, taken
over all `t ∈ T` satisfying `σ(t) + l(t) > d(t)`, of `σ(t) + l(t) - d(t)` is `K` or less?

This is Garey and Johnson's [SS5] SEQUENCING TO MINIMIZE WEIGHTED TARDINESS with release times
added and equal task weights (`1|rⱼ|∑ Tⱼ`), as in the comment to [SS5]. Equal weights `w` are
taken to be `1`, so the weights are not part of the instance: with every weight equal to `w`,
the weighted sum is `w` times the unweighted one, and it is at most `K` exactly when the
unweighted sum is at most `⌊K / w⌋`. Release times and their constraint `σ(t) ≥ r(t)` are those
of [SS1]; a one-processor schedule is Garey and Johnson's [SS1] notion (a one-to-one
`σ : T → ℤ₀⁺` with `σ(t) > σ(t')` implying `σ(t) ≥ σ(t') + l(t')`), the predicate
`IsOneProcessorSchedule` reused from `SequencingToMinimizeWeightedTardinessDefs`, and the
tardiness sum has the same shape as there.

Hardness: Garey and Johnson derive strong NP-completeness from [SS1], which is the case
`K = 0`. [SS5] requires `K ≥ 1`; adding one task with release time and deadline both equal to
the largest deadline `D` and length `1` (tardy by at least `1` in every schedule, by exactly
`1` when started at `D`) and taking `K = 1` reduces the `K = 0` case to it. Membership in NP:
the schedule is a certificate; its start times can be taken below `max r(t) + ∑ l(t)`, so they
have polynomially many bits.

The tasks are `Fin n`, one per listed triple `(l(t), r(t), d(t))`. Binary encoding of all
numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SEQUENCING TO MINIMIZE TOTAL TARDINESS WITH RELEASE TIMES is NP-complete.** Source:
Garey and Johnson (1979), [SS5], comment, and [SS1]; Lenstra, Rinnooy Kan, and Brucker (1977),
Theorems 4(a) and 1(j). -/
public theorem_wanted totalTardinessWithReleaseTimes_npComplete :
    totalTardinessWithReleaseTimesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L totalTardinessWithReleaseTimesDec

end MetaMathlibExt.Complexity.NPComplete.TotalTardinessWithReleaseTimes
