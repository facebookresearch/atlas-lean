/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM WIENER CONNECTOR is NP-complete

Source:
N. Ruchansky, F. Bonchi, D. García-Soriano, F. Gullo and N. Kourtellis, "The minimum Wiener
connector problem", in *Proceedings of the 2015 ACM SIGMOD International Conference on
Management of Data* (2015), 1587-1602, doi:10.1145/2723372.2749449 (Problem 1 and Theorem 2;
arXiv:1504.00513).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumWienerConnectorDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumWienerConnector

/-!
# MINIMUM WIENER CONNECTOR is NP-complete

INSTANCE: a connected graph `G = (V, E)`, a set `Q ⊆ V` of query vertices, and a positive
integer `K`.
QUESTION: is there a set `S ⊆ V` with `Q ⊆ S` such that the induced subgraph `G[S]` is
connected and its Wiener index, the sum of the shortest-path distances `d_{G[S]}(u, v)` over all
unordered pairs `{u, v} ⊆ S`, is at most `K`?

This is the decision version of Problem 1 (Min Wiener Connector) of Ruchansky, Bonchi,
García-Soriano, Gullo and Kourtellis: "Given a graph G = (V, E) and a query set Q ⊆ V, find a
connector H* for Q in G with the smallest Wiener index", where a connector for `Q` is a
connected subgraph of `G` containing `Q`, the input graph is connected, and `W(H)` is the sum
of `d_H(u, v)` over unordered pairs `{u, v} ⊆ V(H)`. As they note, "we may restrict the search
to vertex sets and their corresponding induced subgraphs" (adding edges between chosen vertices
never increases a distance), so a connector is given by its vertex set `S` and is the induced
subgraph `G[S]`. Their Theorem 2 (a gap-preserving reduction from VERTEX COVER in bounded-degree
graphs) shows the problem NP-hard; a certificate is `S`, whose Wiener index is computed by
breadth-first search.

Distances are Mathlib's `SimpleGraph.dist` in `G.induce S`; unordered pairs are the pairs
`u < v` of `S`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM WIENER CONNECTOR is NP-complete.** Source: Ruchansky, Bonchi, García-Soriano,
Gullo and Kourtellis (2015), Problem 1 and Theorem 2. -/
public theorem_wanted minimumWienerConnector_npComplete :
    minimumWienerConnectorDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumWienerConnectorDec

end MetaMathlibExt.Complexity.NPComplete.MinimumWienerConnector
