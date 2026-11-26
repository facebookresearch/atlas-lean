/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF (K_{1,5}, TRIANGLE)-FREE GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY;
F. Maffray and M. Preissmann, "On the NP-completeness of the k-colorability problem for
triangle-free graphs", Discrete Mathematics 162 (1996), 313-317,
doi:10.1016/S0012-365X(97)89267-9;
ISGCI (Information System on Graph Classes and their Inclusions), class `(K_{1,5}, triangle)`-free
(gc_921), problem 3-Colourability: NP-complete [Maffray and Preissmann 1996].
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Star
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityK15TriangleFree

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# 3-COLORABILITY OF (K_{1,5}, TRIANGLE)-FREE GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` with no induced subgraph isomorphic to
the star `K_{1,5}` and no triangle.
QUESTION: is `G` 3-colorable, that is, is there a map `c : V → {1, 2, 3}` with `c(u) ≠ c(v)`
for every edge `uv`?

This is GRAPH K-COLORABILITY (`GraphColoringWanted`, Garey and Johnson [GT4]) with `K = 3`,
restricted to `(K_{1,5}, triangle)`-free graphs. Triangle-freeness is Mathlib's
`SimpleGraph.CliqueFree 3` (no 3-clique; every triangle is induced). The star `K_{1,5}` is
Mathlib's `SimpleGraph.starGraph (0 : Fin 6)` (center `0`, leaves `1, …, 5`), and
`K_{1,5}`-freeness says that `(SimpleGraph.starGraph (0 : Fin 6)).IsIndContained G` (an injective
map that preserves adjacency and non-adjacency) fails. As ISGCI notes, these are precisely the
triangle-free graphs of maximum degree at most 4: in a triangle-free graph the neighbors of a
vertex are pairwise non-adjacent, so five of them would induce `K_{1,5}`. Maffray and Preissmann
prove that 3-COLORABILITY is NP-complete for triangle-free graphs of maximum degree 4; ISGCI
lists 3-Colourability on `(K_{1,5}, triangle)`-free graphs (gc_921) as NP-complete, citing them.

The instance, the graph and the question are those of `GraphColoringWanted`, reused unchanged:
vertex count, edge list on `Fin n` and number of colors `K`, with `GraphColoring.WellFormed`,
`GraphColoring.Graph` and `GraphColoring.GraphColoringFeasible` (`(Graph i).Colorable K`). The
restriction adds `K = 3`, triangle-freeness and `K_{1,5}`-freeness to well-formedness.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with `K = 3`
whose graph has no triangle and no induced star `K_{1,5}`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = 3 ∧ (Graph i).CliqueFree 3 ∧
    ¬ (SimpleGraph.starGraph (0 : Fin 6)).IsIndContained (Graph i)

open Classical in
/-- 3-COLORABILITY OF (K_{1,5}, TRIANGLE)-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def threeColorabilityK15TriangleFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **3-COLORABILITY OF (K_{1,5}, TRIANGLE)-FREE GRAPHS is NP-complete.** Source: Garey and
Johnson (1979), [GT4]; Maffray and Preissmann (1996). -/
public theorem_wanted threeColorabilityK15TriangleFree_npComplete :
    threeColorabilityK15TriangleFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeColorabilityK15TriangleFreeDec

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityK15TriangleFree
