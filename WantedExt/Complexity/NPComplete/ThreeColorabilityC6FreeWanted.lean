/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF C6-FREE GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY;
M. Kamiński and V. V. Lozin, "Coloring edges and vertices of graphs without short or long
cycles", Contributions to Discrete Mathematics 2 (2007), 61-66, doi:10.55016/ojs/cdm.v2i1.61890,
Theorem 2.3;
D. Král', J. Kratochvíl, Zs. Tuza and G. J. Woeginger, "Complexity of coloring graphs without
forbidden induced subgraphs", Graph-Theoretic Concepts in Computer Science (WG 2001), Lecture
Notes in Computer Science 2204 (2001), 254-262, doi:10.1007/3-540-45477-2_23;
P. A. Golovach, M. Johnson, D. Paulusma and J. Song, "A survey on the computational complexity of
coloring graphs with forbidden subgraphs", Journal of Graph Theory 84 (2017), 331-363,
doi:10.1002/jgt.22028, Section 2.1 (before Theorem 4; arXiv:1407.1482v8);
ISGCI (Information System on Graph Classes and their Inclusions), class `C_6`-free (gc_436),
problem 3-Colourability: NP-complete [Král' et al. 2001].
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ThreeColorabilityC6FreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityC6Free

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# 3-COLORABILITY OF C6-FREE GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` with no induced cycle on 6 vertices.
QUESTION: is `G` 3-colorable, that is, is there a map `c : V → {1, 2, 3}` with `c(u) ≠ c(v)`
for every edge `uv`?

This is GRAPH K-COLORABILITY (`GraphColoringWanted`, Garey and Johnson [GT4]) with `K = 3`,
restricted to `C_6`-free graphs. A graph is `C_6`-free when it has no induced subgraph isomorphic
to the cycle `C_6` on 6 vertices: Mathlib's `(SimpleGraph.cycleGraph 6).IsIndContained G` (an
injective map that preserves adjacency and non-adjacency) fails. Kamiński and Lozin, Theorem 2.3:
"For every natural k, g ≥ 3, vertex k-colorability is NP-hard in the class of graphs of girth at
least g". A graph of girth at least 7 has no cycle of length 6, induced or not, so 3-COLORABILITY
stays NP-hard on `C_6`-free graphs; membership in NP is immediate. ISGCI lists 3-Colourability on
`C_6`-free graphs (gc_436) as NP-complete, citing Král', Kratochvíl, Tuza and Woeginger, who
showed the `k = 3` case of large girth while proving that COLORING is NP-complete on `H`-free
graphs whenever `H` contains a cycle (as recorded by Golovach, Johnson, Paulusma and Song,
Section 2.1).

The instance, the graph and the question are those of `GraphColoringWanted`, reused unchanged:
vertex count, edge list on `Fin n` and number of colors `K`, with `GraphColoring.WellFormed`,
`GraphColoring.Graph` and `GraphColoring.GraphColoringFeasible` (`(Graph i).Colorable K`). The
restriction adds `K = 3` and `C_6`-freeness to well-formedness.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **3-COLORABILITY OF C6-FREE GRAPHS is NP-complete.** Source: Garey and Johnson (1979), [GT4];
Kamiński and Lozin (2007), Theorem 2.3; Král', Kratochvíl, Tuza and Woeginger (2001). -/
public theorem_wanted threeColorabilityC6Free_npComplete :
    threeColorabilityC6FreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeColorabilityC6FreeDec

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityC6Free
