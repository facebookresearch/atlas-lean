/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on star convex bipartite graphs: definitions

Source:
W. Jiang, T. Liu, T. Ren and K. Xu, "Two hardness results on feedback vertex sets", Frontiers in
Algorithmics and Algorithmic Aspects in Information and Management (FAW-AAIM 2011), Lecture Notes
in Computer Science 6681 (2011), 233-243, doi:10.1007/978-3-642-21204-8_26;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET (undirected version in
the comment);
ISGCI (https://www.graphclasses.org/classes/gc_1151.html), problem "Feedback vertex set" on star
convex graphs: NP-complete, with the attribution to Jiang, Liu, Ren and Xu.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Star
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetStarConvex

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
  (FeedbackVertexSetInstance Graph FeedbackVertexSetFeasible)

/-- `G` is a star convex bipartite graph: its vertices split into `X` and its complement with
every edge between the two sides, and for some centre `c ∈ X` the star `starGraph c` on `X` makes
the neighbourhood of every vertex outside `X` induce a preconnected subgraph (a subtree) of it. -/
def IsStarConvex {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ X : Set V, (∀ u v, G.Adj u v → (u ∈ X ↔ v ∉ X)) ∧
    ∃ c : X, ∀ y, y ∉ X → ((SimpleGraph.starGraph c).induce {x : X | G.Adj y x}).Preconnected

/-- Well-formedness of an instance: a well-formed FEEDBACK VERTEX SET instance whose graph is
star convex bipartite, with a positive bound `K`. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSet.WellFormed i ∧ IsStarConvex (Graph i) ∧ 0 < i.2.2

open Classical in
/-- FEEDBACK VERTEX SET on star convex bipartite graphs as a decision problem over bitstrings. -/
noncomputable def feedbackVertexSetStarConvexDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetStarConvex
