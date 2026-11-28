/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE TARDY TASKS WITH RELEASE TIMES is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TardyTasksWithReleaseTimesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TardyTasksWithReleaseTimes

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-!
# SEQUENCING TO MINIMIZE TARDY TASKS WITH RELEASE TIMES is NP-complete

INSTANCE: a set `T` of tasks, for each task `t ∈ T` a length `l(t) ∈ ℤ⁺`, a release time
`r(t) ∈ ℤ₀⁺` and a deadline `d(t) ∈ ℤ⁺`, and a positive integer `K ≤ |T|`. QUESTION: is there a
one-processor schedule `σ` for `T` with `σ(t) ≥ r(t)` for all `t ∈ T` such that there are at
most `K` tasks `t ∈ T` for which `σ(t) + l(t) > d(t)`?

This is Garey and Johnson's [SS2] SEQUENCING TO MINIMIZE TARDY TASKS with the partial order `<`
empty and arbitrary release times added (`1|rⱼ|∑ Uⱼ`), as in the comment to [SS2]: polynomial
for `<` empty without release times [Moore, 1968] and with "agreeable" release times, "but is
NP-complete for arbitrary release times (see previous problem)". With `<` empty the precedence
constraints are vacuous and are not part of the instance. Release times and their constraint
`σ(t) ≥ r(t)` are those of [SS1]; a one-processor schedule is Garey and Johnson's [SS1] notion
(a one-to-one `σ : T → ℤ₀⁺` with `σ(t) > σ(t')` implying `σ(t) ≥ σ(t') + l(t')`), the predicate
`IsOneProcessorSchedule` reused from `SequencingToMinimizeWeightedTardinessDefs`.

Hardness: Lenstra, Rinnooy Kan and Brucker (Theorem 4(f)) reduce KNAPSACK to this problem with
bound `0`, and the case `K = 0` is [SS1], NP-complete in the strong sense. [SS2] requires
`K ≥ 1`; adding one task with `l = 2` and `d = 1`, which is tardy in every schedule, and taking
`K = 1` reduces the `K = 0` case to it. Membership in NP: the schedule is a certificate; its
start times can be taken below `max r(t) + ∑ l(t)`, so they have polynomially many bits.

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

/-- **SEQUENCING TO MINIMIZE TARDY TASKS WITH RELEASE TIMES is NP-complete.** Source: Garey
and Johnson (1979), [SS2], comment, and [SS1]; Lenstra, Rinnooy Kan, and Brucker (1977),
Theorem 4(f). -/
public theorem_wanted tardyTasksWithReleaseTimes_npComplete :
    tardyTasksWithReleaseTimesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L tardyTasksWithReleaseTimesDec

end MetaMathlibExt.Complexity.NPComplete.TardyTasksWithReleaseTimes
