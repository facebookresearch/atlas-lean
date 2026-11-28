/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY on (K_4, claw, diamond)-free graphs is NP-complete

Source:
D. Král', J. Kratochvíl, Z. Tuza, and G. J. Woeginger, "Complexity of coloring graphs without
forbidden induced subgraphs", Graph-Theoretic Concepts in Computer Science (WG 2001), LNCS
2204, 254-262, doi:10.1007/3-540-45477-2_23 (3-colorability is NP-complete for
(K₄, K₁,₃, diamond)-free graphs);
P. A. Golovach, M. Johnson, D. Paulusma, and J. Song, "A survey on the computational complexity
of coloring graphs with forbidden subgraphs", Journal of Graph Theory 84 (2017), 331-363,
doi:10.1002/jgt.22028, proof of Theorem 21(i).2 (records that result);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ColoringK4ClawDiamondFreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ColoringK4ClawDiamondFree

/-!
# GRAPH K-COLORABILITY on (K_4, claw, diamond)-free graphs is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` with no induced subgraph isomorphic to
`K_4`, to the claw `K_{1,3}`, or to the diamond (`K_4` minus an edge), and a positive integer
`K`.
QUESTION: is `G` properly `K`-colorable, i.e. is there a map `c : V → {1, …, K}` with
`c(u) ≠ c(v)` for every edge `uv`?

This is GRAPH K-COLORABILITY (`GraphColoringWanted`, Garey and Johnson [GT4]) restricted to the
class of `(K_4, claw, diamond)`-free graphs (ISGCI class `gc_919`). Král', Kratochvíl, Tuza and
Woeginger prove 3-colorability NP-complete on this class, as recorded by Golovach, Johnson,
Paulusma and Song ("3-Colouring is NP-complete ... for (K₄, K₁,₃, co-(2P₁ + P₂))-free graphs";
the complement of `2P₁ + P₂` is the diamond). The instance type, the graph, the parent
well-formedness condition and the question are those of `GraphColoringWanted`
(`GraphColoring.GraphColoringInstance`: vertex count, edge list on `Fin n`, number of colors;
`GraphColoring.Graph`, `GraphColoring.WellFormed`, `GraphColoring.GraphColoringFeasible`, i.e.
`(Graph i).Colorable K`); `WellFormed` adds `0 < K` and the class conditions. `K_4`-free is
Mathlib's `SimpleGraph.CliqueFree 4` (a copy of `K_4` is always induced); the claw is
`completeBipartiteGraph (Fin 1) (Fin 3)` and the diamond is `K_4` on `Fin 4` with the edge
`{0, 1}` deleted; induced subgraphs are Mathlib's `SimpleGraph.IsIndContained` (an embedding
preserving adjacency and non-adjacency), as in `ChromaticNumberHFreeGraphsWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH K-COLORABILITY on `(K_4, claw, diamond)`-free graphs is NP-complete.** Source:
Král', Kratochvíl, Tuza and Woeginger (2001); Golovach, Johnson, Paulusma and Song (2017). -/
public theorem_wanted coloringK4ClawDiamondFree_npComplete :
    coloringK4ClawDiamondFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L coloringK4ClawDiamondFreeDec

end MetaMathlibExt.Complexity.NPComplete.ColoringK4ClawDiamondFree
