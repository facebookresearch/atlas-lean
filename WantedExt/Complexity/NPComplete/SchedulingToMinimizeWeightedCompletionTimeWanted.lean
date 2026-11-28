/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS13] SCHEDULING TO MINIMIZE
WEIGHTED COMPLETION TIME;
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTime

/-!
# SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete

INSTANCE: a set `T` of tasks, a number `m ∈ ℤ⁺` of processors, for each task `t ∈ T` a length
`l(t) ∈ ℤ⁺` and a weight `w(t) ∈ ℤ⁺`, and a positive integer `K`. QUESTION: is there an
`m`-processor schedule `σ` for `T` such that the sum, over all `t ∈ T`, of
`(σ(t) + l(t)) · w(t)` is no more than `K`?

An `m`-processor schedule (Garey and Johnson, [SS8]) is a function `σ : T → ℤ₀⁺` such that, for
all `u ≥ 0`, the number of tasks `t ∈ T` for which `σ(t) ≤ u < σ(t) + l(t)` is no more than `m`.
Tasks are `Fin n`, one per listed pair `(l(t), w(t))`. Binary encoding of all numbers (the
problem remains NP-complete for `m = 2`, where it is solvable in pseudo-polynomial time).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete.** Source: Garey and
Johnson (1979), [SS13]; Lenstra, Rinnooy Kan and Brucker (1977). -/
public theorem_wanted schedulingToMinimizeWeightedCompletionTime_npComplete :
    schedulingToMinimizeWeightedCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L schedulingToMinimizeWeightedCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTime
