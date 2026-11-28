/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNDIRECTED TWO-COMMODITY INTEGRAL FLOW is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND39] UNDIRECTED
TWO-COMMODITY INTEGRAL FLOW;
S. Even, A. Itai, and A. Shamir, "On the complexity of timetable and
multicommodity flow problems", SIAM Journal on Computing 5 (1976), 691-703,
doi:10.1137/0205048.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlowDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlow

/-!
# UNDIRECTED TWO-COMMODITY INTEGRAL FLOW is NP-complete

INSTANCE: a graph `G = (V, E)`, specified vertices `s₁`, `s₂`, `t₁`, `t₂`, a capacity
`c(e) ∈ ℤ⁺` for each `e ∈ E`, and requirements `R₁, R₂ ∈ ℤ⁺`. QUESTION: are there two flow
functions `f₁, f₂ : {(u, v), (v, u) : {u, v} ∈ E} → ℤ₀⁺` such that, for each `{u, v} ∈ E`,
`f₁(u, v) + f₁(v, u) + f₂(u, v) + f₂(v, u) ≤ c({u, v})`, each `fᵢ` is conserved at every vertex
other than `sᵢ` and `tᵢ`, and the net flow of `fᵢ` into `tᵢ` is at least `Rᵢ`, for `i = 1, 2`?

The vertices are `0, ..., n - 1`. Each edge is a record `(u, v, c)`: the edge `{u, v}` with
capacity `c`; there are no self-loops and at most one record per unordered pair. Commodity `i`
is the triple `(sᵢ, tᵢ, Rᵢ)`. A flow is a function `f : Fin n → Fin n → ℕ` (integral and
nonnegative) on ordered pairs. Each commodity's flow is checked with `IsFeasibleFlow` from
`MathlibExt.Combinatorics.Graph.MaxFlowMinCut` against the symmetric capacity `capacity`
(`c({u, v})` on both orientations of an edge, `0` elsewhere), so it vanishes off the two
orientations of the edges and is conserved at every vertex other than its own source and sink.
The joint capacity condition and the requirement on the net flow into `tᵢ` are stated directly.

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

/-- **UNDIRECTED TWO-COMMODITY INTEGRAL FLOW is NP-complete.** Source: Garey and Johnson (1979),
[ND39]; Even, Itai, and Shamir (1976). -/
public theorem_wanted undirectedTwoCommodityIntegralFlow_npComplete :
    undirectedTwoCommodityIntegralFlowDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L undirectedTwoCommodityIntegralFlowDec

end MetaMathlibExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlow
