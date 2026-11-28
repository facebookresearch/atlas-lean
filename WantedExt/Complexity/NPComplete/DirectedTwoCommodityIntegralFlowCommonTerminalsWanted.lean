/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED TWO-COMMODITY INTEGRAL FLOW with s₁ = s₂, t₁ = t₂, restricted arcs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND38] DIRECTED
TWO-COMMODITY INTEGRAL FLOW, p. 216, comment ("Variant in which s₁ = s₂, t₁ = t₂, and arcs
can be restricted to carry only one specified commodity is also NP-complete (follows from
[Even, Itai, and Shamir, 1976])");
S. Even, A. Itai, and A. Shamir, "On the complexity of timetable and
multicommodity flow problems", SIAM Journal on Computing 5 (1976), 691-703,
doi:10.1137/0205048.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowCommonTerminalsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowCommonTerminals

/-!
# DIRECTED TWO-COMMODITY INTEGRAL FLOW with s₁ = s₂, t₁ = t₂, restricted arcs is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s₁ = s₂` and `t₁ = t₂`, a capacity
`c(a) ∈ ℤ⁺` for each `a ∈ A`, requirements `R₁, R₂ ∈ ℤ⁺`, and, for some arcs, a restriction to
carry only one specified commodity. QUESTION: are there two flow functions
`f₁, f₂ : A → ℤ₀⁺` such that `f₁(a) + f₂(a) ≤ c(a)` for each `a ∈ A`, each `fᵢ` is conserved
at every vertex other than `sᵢ` and `tᵢ`, the net flow of `fᵢ` into `tᵢ` is at least `Rᵢ`, for
`i = 1, 2`, and every restricted arc carries no flow of the other commodity?

This is the variant of DIRECTED TWO-COMMODITY INTEGRAL FLOW
(`WantedExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowWanted`) recorded in Garey
and Johnson's comment on [ND38]. An instance is an instance of that problem, whose
`WellFormed` (simple directed graph on `0, ..., n - 1`, positive capacities, terminals in
range, positive requirements) is reused, with the two commodities sharing their source and
their sink, together with a list of restrictions `(u, v, k)`: the arc from `u` to `v` may carry
only commodity `k ∈ {1, 2}`. Each arc has at most one restriction. The question is the
question of that problem, with its `capacity` and `CommodityFlow`, plus the restrictions.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open DirectedTwoCommodityIntegralFlow
  (DirectedTwoCommodityIntegralFlowInstance arcs capacity CommodityFlow)

/-- **DIRECTED TWO-COMMODITY INTEGRAL FLOW with `s₁ = s₂`, `t₁ = t₂` and commodity-restricted
arcs is NP-complete.** Source: Garey and Johnson (1979), [ND38], comment; Even, Itai, and
Shamir (1976). -/
public theorem_wanted directedTwoCommodityIntegralFlowCommonTerminals_npComplete :
    directedTwoCommodityIntegralFlowCommonTerminalsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedTwoCommodityIntegralFlowCommonTerminalsDec

end MetaMathlibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowCommonTerminals
