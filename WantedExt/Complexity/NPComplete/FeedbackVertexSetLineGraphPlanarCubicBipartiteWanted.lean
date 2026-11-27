/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on line graphs of planar cubic bipartite graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET, the problem
restricted here;
A. Munaro, "On line graphs of subcubic triangle-free graphs", Discrete Mathematics 340(6)
(2017), 1210-1226, doi:10.1016/j.disc.2017.01.006, Theorem 24.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.FeedbackVertexSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetLineGraphPlanarCubicBipartite

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet

/-!
# FEEDBACK VERTEX SET on line graphs of planar cubic bipartite graphs is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected) that is the line graph of a planar
cubic bipartite graph, and a nonnegative integer `K`.
QUESTION: is there a set `V' ⊆ V` with `|V'| ≤ K` such that `G - V'` is a forest, that is,
`V'` meets every cycle of `G`?

The instance, its well-formedness and the question are those of the undirected FEEDBACK VERTEX
SET (`WantedExt.Complexity.NPComplete.FeedbackVertexSetWanted`: a simple graph on `Fin n` given
by an edge list and the bound `K`; the question asks for at most `K` vertices whose removal
leaves an acyclic induced subgraph, Mathlib's `SimpleGraph.IsAcyclic`). The restriction adds
that the graph lies in the ISGCI class "line graphs of planar cubic bipartite graphs"
(`gc_1335`): some graph `H` on `Fin m` that is planar (MathlibExt's `SimpleGraph.IsPlanar`, a
crossing-free straight-line drawing, which by Fáry's theorem exists exactly for the planar
graphs), bipartite (Mathlib's `SimpleGraph.IsBipartite`) and cubic (Mathlib's
`SimpleGraph.IsRegularOfDegree 3`) has a line graph isomorphic to `G` (Mathlib's
`SimpleGraph.lineGraph`: one vertex per edge of `H`, two adjacent when the edges are distinct and
share an endpoint; `≃g` is a graph isomorphism). The root graph `H` is not part of the instance.

Munaro, Theorem 24: "Feedback Vertex Set is NP-complete even for line graphs of planar cubic
bipartite graphs", by a reduction from HAMILTONIAN PATH on planar cubic bipartite graphs
(Theorem 23): for such a graph `H` with line graph `G`, the minimum size of a feedback vertex set
of `G` is at least `|V(G)|/3 + 1`, with equality exactly when `H` has a Hamiltonian path
(Theorem 21); its outputs `G = L(H)` lie in the class, so it is a reduction to this problem.
Membership in NP: the certificate is `V'`, the root graph `H` (it has `2|V(G)|/3` vertices, since
`G` has one vertex per edge of the cubic graph `H`) and the isomorphism `G ≃ L(H)`; the verifier
checks the isomorphism, that `H` is cubic and bipartite, that `H` is planar (in linear time, by
Hopcroft and Tarjan, "Efficient planarity testing", Journal of the ACM 21 (1974), 549-568,
doi:10.1145/321850.321852), and that `G - V'` is acyclic, all in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- `G` is the line graph of a planar cubic bipartite graph: some planar, bipartite, 3-regular
graph `H` on `Fin m` has a line graph isomorphic to `G`. -/
def IsLineGraphOfPlanarCubicBipartite {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (m : ℕ) (H : SimpleGraph (Fin m)),
    H.IsPlanar ∧ H.IsBipartite ∧ H.IsRegularOfDegree 3 ∧ Nonempty (G ≃g H.lineGraph)

/-- Well-formedness of an instance: a well-formed FEEDBACK VERTEX SET instance whose graph is the
line graph of a planar cubic bipartite graph. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSet.WellFormed i ∧ IsLineGraphOfPlanarCubicBipartite (Graph i)

open Classical in
/-- FEEDBACK VERTEX SET on line graphs of planar cubic bipartite graphs as a decision problem
over bitstrings. -/
noncomputable def feedbackVertexSetLineGraphPlanarCubicBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetFeasible i)
  | none => false

/-- **FEEDBACK VERTEX SET on line graphs of planar cubic bipartite graphs is NP-complete.**
Source: Garey and Johnson (1979), [GT7]; Munaro (2017), Theorem 24. -/
public theorem_wanted feedbackVertexSetLineGraphPlanarCubicBipartite_npComplete :
    feedbackVertexSetLineGraphPlanarCubicBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetLineGraphPlanarCubicBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetLineGraphPlanarCubicBipartite
