/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET IN TREE CONVEX BIPARTITE GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET;
C. Wang, T. Liu, W. Jiang and K. Xu, "Feedback vertex sets on tree convex bipartite graphs",
Combinatorial Optimization and Applications (COCOA 2012), Lecture Notes in Computer Science 7402
(2012), 95-102, doi:10.1007/978-3-642-31770-5_9;
W. Jiang, T. Liu, T. Ren and K. Xu, "Two hardness results on feedback vertex sets", Frontiers in
Algorithmics and Algorithmic Aspects in Information and Management (FAW-AAIM 2011), Lecture Notes
in Computer Science 6681 (2011), 233-243, doi:10.1007/978-3-642-21204-8_26;
ISGCI (Information System on Graph Classes and their Inclusions), class tree convex (gc_1150),
problem Feedback vertex set: NP-complete [Wang et al. 2012], NP-complete on star convex
[Jiang et al. 2011].
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetTreeConvex

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet (FeedbackVertexSetInstance Graph)

/-- `G` is a tree convex bipartite graph: for some vertex set `X` with every edge joining `X` to
its complement, there is a tree `T` on `X` in which the neighbourhood of every vertex outside `X`
induces a connected subgraph (a subtree). -/
def IsTreeConvex {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ X : Set (Fin n), G.IsBipartiteWith X Xᶜ ∧
    ∃ T : SimpleGraph X, T.IsTree ∧ ∀ y ∉ X, (T.induce {x : X | G.Adj y x}).Connected

/-- Well-formedness of an instance: a well-formed FEEDBACK VERTEX SET instance whose graph is
tree convex bipartite. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSet.WellFormed i ∧ IsTreeConvex (Graph i)

open Classical in
/-- FEEDBACK VERTEX SET IN TREE CONVEX BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def feedbackVertexSetTreeConvexDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSet.FeedbackVertexSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetTreeConvex
