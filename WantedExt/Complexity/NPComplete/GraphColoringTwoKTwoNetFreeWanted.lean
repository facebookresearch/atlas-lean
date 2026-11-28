/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY ON (2K₂, NET)-FREE GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER), the problem restricted here;
D. Schindl, "Some new hereditary classes where graph coloring remains NP-hard", Discrete
Mathematics 295 (2005), 197-202, doi:10.1016/j.disc.2005.03.003;
P. A. Golovach, M. Johnson, D. Paulusma, and J. Song, "A survey on the computational complexity
of coloring graphs with forbidden subgraphs", Journal of Graph Theory 84 (2017), 331-363,
doi:10.1002/jgt.22028, arXiv:1407.1482, Theorem 17 (Schindl's theorem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GraphColoringTwoKTwoNetFreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoringTwoKTwoNetFree

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# GRAPH K-COLORABILITY ON (2K₂, NET)-FREE GRAPHS is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected) with no induced subgraph isomorphic
to `2K₂` and none isomorphic to the net, and a positive integer `K ≤ |V|`.
QUESTION: is `G` `K`-colorable, i.e. is there a map `c : V → {1, …, K}` with `c(u) ≠ c(v)` for
every edge `uv`?

This is GRAPH K-COLORABILITY restricted to the class of `(2K₂, net)`-free graphs (ISGCI class
`gc_927`). Schindl proves that GRAPH COLORING remains NP-hard on `(H₁, …, H_p)`-free graphs
whenever the complement of each `Hᵢ` has a connected component that is neither a path nor the
line graph of a subdivided claw; the complement of `2K₂` is `C₄` and the complement of the net is
the 3-sun, so this applies, as Golovach, Johnson, Paulusma, and Song record (Theorem 17). Membership
in NP is immediate (a coloring is a certificate).

The instance, the graph and the question are those of `GraphColoringWanted`, reused unchanged:
vertex count, edge list on `Fin n` and number of colors `K`, with `GraphColoring.WellFormed`,
`GraphColoring.Graph` and `GraphColoring.GraphColoringFeasible` (`(Graph i).Colorable i.2.2`). The
restriction adds `0 < K ≤ |V|` (the bound of Garey and Johnson's [GT4]) and the two forbidden
induced subgraphs. `2K₂` (two disjoint edges) is `SimpleGraph.pathGraph 2 ⊕g SimpleGraph.pathGraph
2`; the net is a triangle with one pendant vertex attached to each of its vertices (ISGCI `net =
S₃`). Induced subgraphs are Mathlib's `SimpleGraph.IsIndContained` (an embedding that preserves
adjacency and non-adjacency), as in `ChromaticNumberHFreeGraphsWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH K-COLORABILITY ON (2K₂, NET)-FREE GRAPHS is NP-complete.** Source: Garey and Johnson
(1979), [GT4]; Schindl (2005); Golovach, Johnson, Paulusma, and Song (2017), Theorem 17. -/
public theorem_wanted graphColoringTwoKTwoNetFree_npComplete :
    graphColoringTwoKTwoNetFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphColoringTwoKTwoNetFreeDec

end MetaMathlibExt.Complexity.NPComplete.GraphColoringTwoKTwoNetFree
