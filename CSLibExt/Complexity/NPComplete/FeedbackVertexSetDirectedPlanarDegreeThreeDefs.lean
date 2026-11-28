/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET (planar digraphs with in- and out-degree at most 3): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET,
pp. 191-192 (comment: "Remains NP-complete [...] for planar digraphs with no in- or out-degree
exceeding 3 [Garey and Johnson, ——]", unpublished);
T. Bai, Y. Cao and M. Xiao, "Feedback set problems on bounded-degree (planar) graphs",
arXiv:2605.11407 (2026), Theorem 8 (planar digraphs with in- and out-degree at most 2).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetDirectedDegreeTwoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetDirectedPlanarDegreeThree

open FeedbackVertexSetDirectedDegreeTwo (FeedbackVertexSetDirectedInstance SimpleArcs
  DegreeAtMost FeedbackVertexSetDirectedFeasible)

/-- The underlying undirected simple graph: `u` and `v` are adjacent when `u ≠ v` and `u → v`
or `v → u` is an arc. -/
def UnderlyingGraph (i : FeedbackVertexSetDirectedInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the digraph has no loops or multiple arcs, its underlying
graph is planar, every vertex has in-degree and out-degree at most 3, and `0 < K ≤ |V|`. -/
def WellFormed (i : FeedbackVertexSetDirectedInstance) : Prop :=
  SimpleArcs i ∧ (UnderlyingGraph i).IsPlanar ∧ DegreeAtMost i 3 ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- FEEDBACK VERTEX SET on planar digraphs with in- and out-degree at most 3, as a decision
problem over bitstrings. -/
noncomputable def feedbackVertexSetDirectedPlanarDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeedbackVertexSetDirectedInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetDirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetDirectedPlanarDegreeThree
