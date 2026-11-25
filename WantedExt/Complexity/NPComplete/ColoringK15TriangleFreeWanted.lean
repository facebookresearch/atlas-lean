/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY on (K_1,5, triangle)-free graphs is NP-complete

Source:
F. Maffray and M. Preissmann, "On the NP-completeness of the k-colorability problem for
triangle-free graphs", Discrete Mathematics 162 (1996), 313-317,
doi:10.1016/S0012-365X(97)89267-9 (3-colorability is NP-complete for triangle-free graphs of
maximum degree 4);
P. A. Golovach, M. Johnson, D. Paulusma, and J. Song, "A survey on the computational complexity
of coloring graphs with forbidden subgraphs", Journal of Graph Theory 84 (2017), 331-363,
doi:10.1002/jgt.22028, Theorem 16 and Theorem 21(i).6 ("3-Colouring is NP-complete for
(C₃, K₁,ᵣ)-free graphs for all r ≥ 5");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ColoringK15TriangleFree

/-!
# GRAPH K-COLORABILITY on (K_1,5, triangle)-free graphs is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` with no induced subgraph isomorphic to
the star `K_{1,5}` and no triangle, and a positive integer `K`.
QUESTION: is `G` properly `K`-colorable, i.e. is there a map `c : V → {1, …, K}` with
`c(u) ≠ c(v)` for every edge `uv`?

This is GRAPH K-COLORABILITY (`GraphColoringWanted`, Garey and Johnson [GT4]) restricted to the
class of `(K_{1,5}, C₃)`-free graphs (ISGCI class `gc_921`). In a triangle-free graph the
neighbors of a vertex are pairwise non-adjacent, so the class consists of the triangle-free
graphs of maximum degree at most `4`; Maffray and Preissmann prove 3-colorability NP-complete
there, which Golovach, Johnson, Paulusma and Song record as NP-completeness of 3-colorability
for `(C₃, K_{1,r})`-free graphs, `r ≥ 5`. The instance type, the graph, the parent
well-formedness condition and the question are those of `GraphColoringWanted`
(`GraphColoring.GraphColoringInstance`: vertex count, edge list on `Fin n`, number of colors;
`GraphColoring.Graph`, `GraphColoring.WellFormed`, `GraphColoring.GraphColoringFeasible`, i.e.
`(Graph i).Colorable K`); `WellFormed` adds `0 < K` and the class conditions. Triangle-free is
Mathlib's `SimpleGraph.CliqueFree 3` (a triangle is a 3-clique, and every triangle is induced);
`K_{1,5}` is `completeBipartiteGraph (Fin 1) (Fin 5)`, and induced subgraphs are Mathlib's
`SimpleGraph.IsIndContained` (an embedding preserving adjacency and non-adjacency), as in
`ChromaticNumberHFreeGraphsWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance (a simple graph
given by an edge list), `K` is positive, the graph has no triangle, and `K_{1,5}` is not an
induced subgraph of it. -/
def WellFormed (i : GraphColoring.GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2 ∧ (GraphColoring.Graph i).CliqueFree 3 ∧
    ¬ (completeBipartiteGraph (Fin 1) (Fin 5)).IsIndContained (GraphColoring.Graph i)

open Classical in
/-- GRAPH K-COLORABILITY on `(K_{1,5}, triangle)`-free graphs as a decision problem over
bitstrings. -/
noncomputable def coloringK15TriangleFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoring.GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **GRAPH K-COLORABILITY on `(K_{1,5}, triangle)`-free graphs is NP-complete.** Source:
Maffray and Preissmann (1996); Golovach, Johnson, Paulusma and Song (2017), Theorem 21(i).6. -/
public theorem_wanted coloringK15TriangleFree_npComplete :
    coloringK15TriangleFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L coloringK15TriangleFreeDec

end MetaMathlibExt.Complexity.NPComplete.ColoringK15TriangleFree
