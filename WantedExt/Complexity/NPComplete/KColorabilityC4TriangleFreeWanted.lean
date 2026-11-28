/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY OF (C4,TRIANGLE)-FREE GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER), the problem restricted here;
D. Král', J. Kratochvíl, Zs. Tuza and G. J. Woeginger, "Complexity of coloring graphs without
forbidden induced subgraphs", Graph-Theoretic Concepts in Computer Science (WG 2001), Lecture
Notes in Computer Science 2204 (2001), 254-262, doi:10.1007/3-540-45477-2_23;
M. Kamiński and V. V. Lozin, "Coloring edges and vertices of graphs without short or long
cycles", Contributions to Discrete Mathematics 2 (2007), 61-66,
doi:10.55016/ojs/cdm.v2i1.61890, Theorem 2.3 and Corollary 2.4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.KColorabilityC4TriangleFreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KColorabilityC4TriangleFree

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance)

/-!
# GRAPH K-COLORABILITY OF (C4,TRIANGLE)-FREE GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` with no induced subgraph isomorphic to
the cycle `C_4` on 4 vertices and no triangle, and a positive integer `K`.
QUESTION: is `G` `K`-colorable, i.e. is there a map `c : V → {1, …, K}` with `c(u) ≠ c(v)` for
every edge `uv`?

This is GRAPH K-COLORABILITY (Garey and Johnson [GT4]), with `K` part of the instance,
restricted to the class of `(C_4, triangle)`-free graphs (ISGCI class `gc_911`). It restricts
CHROMATIC NUMBER OF H-FREE GRAPHS (`ChromaticNumberHFreeGraphsWanted`) for `H = C_4`, whose
instance type, graph, well-formedness and question are reused: a vertex count, an edge list on
`Fin n` and a bound `K` (`GraphColoring.GraphColoringInstance`, `GraphColoring.Graph`), the
well-formedness `ChromaticNumberHFreeGraphs.WellFormed (SimpleGraph.cycleGraph 4)` (a simple edge
list, `0 < K`, and no induced `C_4`), and the question `GraphColoring.GraphColoringFeasible`
(`(Graph i).Colorable K`). The restriction adds that the graph has no triangle: Mathlib's
`SimpleGraph.CliqueFree 3` (no 3-clique; a 3-clique is always induced, so this is the same as
having no induced triangle). A graph is `C_4`-free when Mathlib's
`(SimpleGraph.cycleGraph 4).IsIndContained G` (an embedding of `C_4` into `G` that preserves
adjacency and non-adjacency) fails.

In a triangle-free graph every 4-cycle is induced, since a chord of a 4-cycle closes a triangle;
so the `(C_4, triangle)`-free graphs are exactly the graphs with no cycle of length 3 or 4, the
graphs of girth at least 5. Kamiński and Lozin, Theorem 2.3, prove vertex `k`-colorability
NP-hard in the class of graphs of girth at least `g` for all `k, g ≥ 3`, and state as Corollary
2.4 that vertex colorability (the number of colors in the input) is NP-hard in the class of graphs
of girth at least `g` for every `g ≥ 3`; for `g = 5` that is this problem. ISGCI records the
problem as NP-complete on this class with Král', Kratochvíl, Tuza and Woeginger as the reference.
Membership in NP is immediate (a coloring is a certificate).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH K-COLORABILITY OF (C4,TRIANGLE)-FREE GRAPHS is NP-complete.** Source: Garey and
Johnson (1979), [GT4]; Král', Kratochvíl, Tuza and Woeginger (2001); Kamiński and Lozin (2007),
Corollary 2.4. -/
public theorem_wanted kColorabilityC4TriangleFree_npComplete :
    kColorabilityC4TriangleFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kColorabilityC4TriangleFreeDec

end MetaMathlibExt.Complexity.NPComplete.KColorabilityC4TriangleFree
