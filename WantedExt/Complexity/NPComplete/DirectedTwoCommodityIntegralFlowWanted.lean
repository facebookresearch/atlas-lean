/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED TWO-COMMODITY INTEGRAL FLOW is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND38] DIRECTED
TWO-COMMODITY INTEGRAL FLOW;
S. Even, A. Itai, and A. Shamir, "On the complexity of timetable and
multicommodity flow problems", SIAM Journal on Computing 5 (1976), 691-703,
doi:10.1137/0205048.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlow

/-!
# DIRECTED TWO-COMMODITY INTEGRAL FLOW is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s₁`, `s₂`, `t₁`, `t₂`, a capacity
`c(a) ∈ ℤ⁺` for each `a ∈ A`, and requirements `R₁, R₂ ∈ ℤ⁺`. QUESTION: are there two flow
functions `f₁, f₂ : A → ℤ₀⁺` such that `f₁(a) + f₂(a) ≤ c(a)` for each `a ∈ A`, each `fᵢ` is
conserved at every vertex other than `sᵢ` and `tᵢ`, and the net flow of `fᵢ` into `tᵢ` is at
least `Rᵢ`, for `i = 1, 2`?

The vertices are `0, ..., n - 1`. Each arc is a record `(u, v, c)`: the arc from `u` to `v` with
capacity `c`; there are no self-loops and no repeated arcs. Commodity `i` is the triple
`(sᵢ, tᵢ, Rᵢ)`. A flow is a function `f : Fin n → Fin n → ℕ` (integral and nonnegative) on
ordered pairs. Each commodity's flow is checked with `IsFeasibleFlow` from
`MathlibExt.Combinatorics.Graph.MaxFlowMinCut` against the arc capacities `capacity` (`c(a)` on
an arc `a`, `0` on every other ordered pair), so it vanishes off the arcs (it is a function on
`A`) and is conserved at every vertex other than its own source and sink. The joint capacity
constraint and the requirement on the net flow into `tᵢ` are stated directly.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/-- **DIRECTED TWO-COMMODITY INTEGRAL FLOW is NP-complete.** Source: Garey and Johnson (1979),
[ND38]; Even, Itai, and Shamir (1976). -/
public theorem_wanted directedTwoCommodityIntegralFlow_npComplete :
    directedTwoCommodityIntegralFlowDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedTwoCommodityIntegralFlowDec

end MetaMathlibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlow
