/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHAIN GRAPH COMPLETION is NP-complete

Source:
M. Yannakakis, "Computing the minimum fill-in is NP-complete", SIAM Journal on Algebraic and
Discrete Methods 2 (1981), 77-79, doi:10.1137/0602010;
A. Natanzon, R. Shamir and R. Sharan, "Complexity classification of some edge modification
problems", Discrete Applied Mathematics 113 (2001), 109-128,
doi:10.1016/S0166-218X(00)00391-7, Section 3.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ChainGraphCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainGraphCompletion

/-!
# CHAIN GRAPH COMPLETION is NP-complete

INSTANCE: a bipartite graph `G = (P, Q, E)` with `E ⊆ P × Q`, the bipartition given, and a
nonnegative integer `K`.
QUESTION: can at most `K` edges between `P` and `Q` be added so that the result is a chain
graph, i.e., so that the neighborhoods `N(v)`, `v ∈ P`, are totally ordered by inclusion?

Natanzon, Shamir and Sharan (Section 3.1) define a bipartite graph `(P, Q, E)` to be a chain
graph if the vertices of `P` can be ordered `π(1), …, π(|P|)` with
`N(π(1)) ⊆ N(π(2)) ⊆ … ⊆ N(π(|P|))`, record that Yannakakis introduced the class and proved
CHAIN COMPLETION NP-complete, and note that the bipartition is part of the input. A finite
family of sets admits such an ordering exactly when any two of its members are comparable
under inclusion, which is how `IsChainGraph` states it.

The sides are `P = Fin p` and `Q = Fin q`; an edge is a pair `(a, b)` with `a ∈ P` and `b ∈ Q`,
as in `MaximumEdgeBicliqueWanted`. The completed graph is given by its edge set `F`, a finite
set of pairs containing the edges of `G`; the added edges are `F \ E`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CHAIN GRAPH COMPLETION is NP-complete.** Source: Yannakakis (1981); Natanzon, Shamir and
Sharan (2001), Section 3.1. -/
public theorem_wanted chainGraphCompletion_npComplete :
    chainGraphCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chainGraphCompletionDec

end MetaMathlibExt.Complexity.NPComplete.ChainGraphCompletion
