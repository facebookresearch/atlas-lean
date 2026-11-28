/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# VERTEX RANKING (TREE-DEPTH) is NP-complete

Source:
H. L. Bodlaender, J. S. Deogun, K. Jansen, T. Kloks, D. Kratsch, H. Müller and Zs. Tuza,
"Rankings of graphs", SIAM Journal on Discrete Mathematics 11(1) (1998), 168-181,
doi:10.1137/S0895480195282550;
A. Pothen, "The complexity of optimal elimination trees", Technical Report CS-88-13, Department
of Computer Science, Pennsylvania State University (1988);
I. Karpas, O. Neiman and S. Smorodinsky, "On vertex rankings of graphs and its relatives",
Discrete Mathematics 338(8) (2015), 1460-1467, doi:10.1016/j.disc.2015.03.008, arXiv:1609.06111
(definition, Section 1).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.VertexRankingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.VertexRanking

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# VERTEX RANKING (TREE-DEPTH) is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`.

QUESTION: does `G` have a vertex ranking with `K` colors, that is, a coloring
`c : V → {1, …, K}` such that for any two distinct vertices `u, v` with `c(u) = c(v)`, every path
between `u` and `v` contains a vertex `w` with `c(w) > c(u)`?

The least such `K` is the vertex ranking number `χ_r(G)`, which equals the tree-depth of `G`:
the minimum height, counted in vertices, of a rooted forest on `V` in which every edge of `G`
joins an ancestor and a descendant (an elimination forest; for a connected graph, an elimination
tree). Bodlaender et al. (1998) introduce the problem as VERTEX RANKING. Karpas, Neiman and
Smorodinsky (Section 1) state the definition used here ("if `c(u) = c(v)` then any simple path
between `u, v` contains a vertex `w` with `c(w) > c(u)`") and record that the problem is NP-hard
on bipartite and co-bipartite graphs, citing Bodlaender et al.; NP-completeness for general
graphs is due to Pothen (1988), whose report was not available. Membership in NP: a ranking is a
certificate, checked by testing, for each color `j` and each pair of vertices of color `j`,
whether they are connected in the graph induced by the vertices of color at most `j`.

The instance, the graph and the simple-graph condition are those of
`WantedExt.Complexity.NPComplete.GraphColoringWanted` (`GraphColoring.GraphColoringInstance`: a
vertex count `n`, vertices `Fin n`, an edge list and the number `K` of colors;
`GraphColoring.Graph`; `GraphColoring.WellFormed`). Colors are `Fin K` (color `j` stands for
`j + 1`), and paths are Mathlib walks with `SimpleGraph.Walk.IsPath`. Taking `u, v` adjacent
shows that a ranking is a proper coloring.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **VERTEX RANKING (TREE-DEPTH) is NP-complete.** Source: Bodlaender et al. (1998);
Pothen (1988). -/
public theorem_wanted vertexRanking_npComplete :
    vertexRankingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L vertexRankingDec

end MetaMathlibExt.Complexity.NPComplete.VertexRanking
