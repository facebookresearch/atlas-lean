/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACHROMATIC NUMBER of complements of bipartite graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT5] ACHROMATIC NUMBER, p. 191
(comment: "Remains NP-complete even if `G` is the complement of a bipartite graph and hence has
no independent set of more than two vertices.");
M. Yannakakis and F. Gavril, "Edge dominating sets in graphs", SIAM Journal on Applied
Mathematics 38 (1980), 364-372, doi:10.1137/0138030, Corollary 2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.AchromaticNumberCoBipartiteDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AchromaticNumberCoBipartite

open MetaMathlibExt.Complexity.NPComplete.AchromaticNumber (AchromaticNumberInstance)

/-!
# ACHROMATIC NUMBER of complements of bipartite graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is the complement of a bipartite graph, and a positive
integer `K ≤ |V|`.
QUESTION: does `G` have achromatic number `K` or greater, i.e., is there a partition of `V` into
disjoint sets `V₁, V₂, ..., V_k`, `k ≥ K`, such that each `Vᵢ` is an independent set for `G` and,
for each pair of distinct sets `Vᵢ, Vⱼ`, `Vᵢ ∪ Vⱼ` is not an independent set for `G`?

This is ACHROMATIC NUMBER ([GT5], `AchromaticNumberWanted`) restricted to complements of
bipartite graphs. Yannakakis and Gavril (Corollary 2) prove that the achromatic number problem
is NP-complete even for complements of bipartite graphs.

The instance and the question are those of `AchromaticNumberWanted`, reused unchanged: vertex
count, edge list on `Fin n` and bound `K`, with `AchromaticNumber.WellFormed` (simple edge list)
and `AchromaticNumber.AchromaticNumberFeasible` (some `q ≥ K` and a proper coloring with colors
`0, …, q - 1`, all used, every two of them adjacent somewhere; its color classes are the sets
`Vᵢ`). The restriction adds to well-formedness that the complement of the graph
`Cslib.Complexity.Karp.edgeGraph n E` is bipartite (Mathlib's `SimpleGraph.IsBipartite`, as in
`TreewidthCoBipartiteWanted`), and the bound `0 < K ≤ |V|` of the instance class of [GT5].

The vertex count is a binary number, but the vertex set of a complement of a bipartite graph is
covered by two cliques, so `|V| ≤ 2 + 2 √|E|` and the edge list is not succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ACHROMATIC NUMBER is NP-complete for complements of bipartite graphs.** Source: Garey and
Johnson (1979), [GT5], comment; Yannakakis and Gavril (1980), Corollary 2. -/
public theorem_wanted achromaticNumberCoBipartite_npComplete :
    achromaticNumberCoBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L achromaticNumberCoBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.AchromaticNumberCoBipartite
