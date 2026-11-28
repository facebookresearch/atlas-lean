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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TotalCompletionTimeWithReleaseTimesDefs

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
predicate `IsOneProcessorSchedule` is reused from `SequencingToMinimizeWeightedTardinessDefs`.
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

/-- **SEQUENCING TO MINIMIZE TOTAL COMPLETION TIME WITH RELEASE TIMES is NP-complete.**
Source: Garey and Johnson (1979), [SS4]; Lenstra, Rinnooy Kan, and Brucker (1977),
Theorem 4(a). -/
public theorem_wanted totalCompletionTimeWithReleaseTimes_npComplete :
    totalCompletionTimeWithReleaseTimesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L totalCompletionTimeWithReleaseTimesDec

end MetaMathlibExt.Complexity.NPComplete.TotalCompletionTimeWithReleaseTimes
