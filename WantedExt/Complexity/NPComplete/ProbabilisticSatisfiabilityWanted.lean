/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PROBABILISTIC SATISFIABILITY is NP-complete

Source:
G. Georgakopoulos, D. Kavvadias, and C. H. Papadimitriou, "Probabilistic satisfiability",
Journal of Complexity 4 (1988), 1-11, doi:10.1016/0885-064X(88)90006-4;
M. Finger and G. De Bona, "A logic based algorithm for solving probabilistic satisfiability",
Advances in Artificial Intelligence (IBERAMIA 2010), Lecture Notes in Computer Science, 453-462,
doi:10.1007/978-3-642-16952-6_46, Section 2 (the problem, Proposition 1 of Georgakopoulos et al.,
and NP-completeness).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ProbabilisticSatisfiabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ProbabilisticSatisfiability

/-!
# PROBABILISTIC SATISFIABILITY is NP-complete

INSTANCE: clauses `C₁, …, Cₘ` over the variables `x₁, …, xₙ` and rationals `p₁, …, pₘ` in
`[0, 1]`.
QUESTION: is there a probability distribution `π` on the `2ⁿ` truth assignments (valuations) of
`x₁, …, xₙ` under which each clause `Cᵢ` holds with probability exactly `pᵢ`, i.e.,
`P_π(Cᵢ) = Σ {π(v) | v(Cᵢ) = 1} = pᵢ` (Finger and De Bona, Section 2)?

Georgakopoulos, Kavvadias and Papadimitriou show that a satisfiable instance has a distribution
supported on at most `m + 1` assignments, which gives membership in NP, and that the problem is
NP-hard, even for clauses of at most two literals; SAT is the special case where every `pᵢ = 1`.

Clauses are `Cslib.Logic.LegacyPL.CNFClause`s, lists of literals `(variable, polarity)`; the
variables are `0, …, n - 1`, and an assignment `v : Fin n → Bool` is read on all variables by
`extend`. A distribution is a nonnegative real function on assignments summing to `1`. A probability
`pᵢ = aᵢ / bᵢ` is given as two naturals with `bᵢ > 0` and `aᵢ ≤ bᵢ`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PROBABILISTIC SATISFIABILITY is NP-complete.** Source: Georgakopoulos, Kavvadias and
Papadimitriou (1988); Finger and De Bona (2010), Section 2. -/
public theorem_wanted probabilisticSatisfiability_npComplete :
    probabilisticSatisfiabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L probabilisticSatisfiabilityDec

end MetaMathlibExt.Complexity.NPComplete.ProbabilisticSatisfiability
