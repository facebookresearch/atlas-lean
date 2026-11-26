/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF LINEAR DOMINO GRAPHS OF MAXIMUM DEGREE 4 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY;
Yu. Metelsky and R. Tyshkevich, "Line graphs of Helly hypergraphs", SIAM Journal on Discrete
Mathematics 16 (2003), 438-448, doi:10.1137/S089548019936521X;
D. Král', J. Kratochvíl, Zs. Tuza and G. J. Woeginger, "Complexity of coloring graphs without
forbidden induced subgraphs", Graph-Theoretic Concepts in Computer Science (WG 2001), Lecture
Notes in Computer Science 2204 (2001), 254-262, doi:10.1007/3-540-45477-2_23;
ISGCI (Information System on Graph Classes and their Inclusions), class linear domino ∩ maximum
degree 4 (gc_718), problem 3-Colourability: NP-complete [Metelsky and Tyshkevich 2003], and
NP-complete on `(K_4, claw, diamond)`-free graphs [Král' et al. 2001].
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Star
public import Mathlib.Data.Set.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityLinearDominoMaxDegreeFour

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# 3-COLORABILITY OF LINEAR DOMINO GRAPHS OF MAXIMUM DEGREE 4 is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is a linear domino graph and has
maximum degree at most 4.
QUESTION: is `G` 3-colorable, that is, is there a map `c : V → {1, 2, 3}` with `c(u) ≠ c(v)`
for every edge `uv`?

This is GRAPH K-COLORABILITY (`GraphColoringWanted`, Garey and Johnson [GT4]) with `K = 3`,
restricted to the ISGCI class linear domino ∩ maximum degree 4 (gc_718). In ISGCI's words, a
graph is a domino if every vertex is contained in at most two maximal cliques, and a domino is
linear if every edge belongs to exactly one maximal clique; a graph has maximum degree 4 when no
vertex has more than 4 neighbours. ISGCI records, citing Metelsky and Tyshkevich, that the linear
domino graphs are exactly the `(claw, diamond)`-free graphs, and lists gc_718 as equivalent to
`(XC_11, claw, diamond)`-free, where `XC_11`-freeness is maximum degree at most 4. The module
states the class in this forbidden-subgraph form: no induced claw `K_{1,3}`, no induced diamond
`K_4 - e`, and every vertex has at most 4 neighbors. (The equivalence is elementary. An edge `uv`
in two maximal cliques gives `x` in one and `y` in the other with `x`, `y` non-adjacent, and
`u, v, x, y` induce a diamond; conversely the two triangles of a diamond lie in different maximal
cliques through its middle edge. Three pairwise non-adjacent neighbors of a vertex lie in three
different maximal cliques through it, so a domino is claw-free; and in a `(claw, diamond)`-free
graph the neighborhood of a vertex is a disjoint union of at most two cliques, so the vertex lies
in at most two maximal cliques.)

Induced subgraphs are Mathlib's `SimpleGraph.IsIndContained` (an injective map that preserves
adjacency and non-adjacency); the claw is Mathlib's star `SimpleGraph.starGraph (0 : Fin 4)`
(center `0`, leaves `1, 2, 3`); the diamond is the complete graph on `Fin 4` with the edge
`{0, 1}` deleted, `(⊤ : SimpleGraph (Fin 4)).deleteEdges {s(0, 1)}`; the degree bound counts
neighbors with `Set.ncard` of `SimpleGraph.neighborSet`, as in
`PlanarDegreeFourThreeColorabilityWanted`.

ISGCI lists 3-Colourability on gc_718 as NP-complete, citing Metelsky and Tyshkevich, and also
as NP-complete on its subclass of `(K_4, claw, diamond)`-free graphs, citing Král', Kratochvíl,
Tuza and Woeginger: in a `(claw, diamond)`-free graph without `K_4`, the neighborhood of a vertex
is a disjoint union of at most two cliques of size at most 2, so every vertex has at most 4
neighbors.

The instance, the graph and the question are those of `GraphColoringWanted`, reused unchanged:
vertex count, edge list on `Fin n` and number of colors `K`, with `GraphColoring.WellFormed`,
`GraphColoring.Graph` and `GraphColoring.GraphColoringFeasible` (`(Graph i).Colorable K`). The
restriction adds `K = 3`, claw-freeness, diamond-freeness and the degree bound to
well-formedness.

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
whose graph is linear domino (no induced claw `K_{1,3}` and no induced diamond `K_4 - e`) and has
maximum degree at most 4. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = 3 ∧
    ¬ (SimpleGraph.starGraph (0 : Fin 4)).IsIndContained (Graph i) ∧
    ¬ ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(0, 1)}).IsIndContained (Graph i) ∧
    ∀ v : Fin i.1, ((Graph i).neighborSet v).ncard ≤ 4

open Classical in
/-- 3-COLORABILITY OF LINEAR DOMINO GRAPHS OF MAXIMUM DEGREE 4 as a decision problem over
bitstrings. -/
noncomputable def threeColorabilityLinearDominoMaxDegreeFourDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **3-COLORABILITY OF LINEAR DOMINO GRAPHS OF MAXIMUM DEGREE 4 is NP-complete.** Source: Garey
and Johnson (1979), [GT4]; Metelsky and Tyshkevich (2003); Král', Kratochvíl, Tuza and Woeginger
(2001). -/
public theorem_wanted threeColorabilityLinearDominoMaxDegreeFour_npComplete :
    threeColorabilityLinearDominoMaxDegreeFourDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeColorabilityLinearDominoMaxDegreeFourDec

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityLinearDominoMaxDegreeFour
