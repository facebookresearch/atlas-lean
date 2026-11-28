/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET (planar digraphs with in- and out-degree at most 3) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET,
pp. 191-192 (comment: "Remains NP-complete [...] for planar digraphs with no in- or out-degree
exceeding 3 [Garey and Johnson, ——]", unpublished);
T. Bai, Y. Cao and M. Xiao, "Feedback set problems on bounded-degree (planar) graphs",
arXiv:2605.11407 (2026), Theorem 8 (planar digraphs with in- and out-degree at most 2).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetDirectedPlanarDegreeThreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetDirectedPlanarDegreeThree

open FeedbackVertexSetDirectedDegreeTwo (FeedbackVertexSetDirectedInstance SimpleArcs
  DegreeAtMost FeedbackVertexSetDirectedFeasible)

/-!
# FEEDBACK VERTEX SET (planar digraphs with in- and out-degree at most 3) is NP-complete

INSTANCE: a directed graph `G = (V, A)` that is planar and in which no vertex has in-degree or
out-degree exceeding 3, and a positive integer `K ≤ |V|`.
QUESTION: is there a subset `V' ⊆ V` with `|V'| ≤ K` such that `V'` contains at least one vertex
from every directed cycle in `G`?

The instance type, the digraph conditions (`SimpleArcs`: no loops or multiple arcs; opposite
arcs allowed), the degree bound (`DegreeAtMost`) and the question
(`FeedbackVertexSetDirectedFeasible`, whose directed cycles are MathlibExt's
`SimpleGraph.IsDirectedCycle`) are those of `FeedbackVertexSetDirectedDegreeTwoWanted`,
reused unchanged; this module bounds the degrees by 3 instead of 2 and adds planarity. A
digraph is planar when its underlying undirected graph is, so planarity is the shared
MathlibExt predicate `SimpleGraph.IsPlanar` applied to `Cslib.Complexity.Karp.edgeGraph n A`,
the simple graph joining `u` and `v` when either arc is present, as in
`PlanarDegreeTwoDirectedHamiltonianCircuitWanted`.

Bai, Cao and Xiao prove NP-completeness already for planar digraphs with in- and out-degree
at most 2, which are among the instances here.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FEEDBACK VERTEX SET is NP-complete on planar digraphs with in- and out-degree at most
3.** Source: Garey and Johnson (1979), [GT7], comment; Bai, Cao and Xiao (2026), Theorem 8. -/
public theorem_wanted feedbackVertexSetDirectedPlanarDegreeThree_npComplete :
    feedbackVertexSetDirectedPlanarDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetDirectedPlanarDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetDirectedPlanarDegreeThree
