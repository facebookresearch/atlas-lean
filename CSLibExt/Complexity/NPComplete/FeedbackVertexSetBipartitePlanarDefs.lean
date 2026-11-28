/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on planar bipartite graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET, the problem
restricted here;
A. Takaoka, S. Tayu and S. Ueno, "On minimum feedback vertex sets in bipartite graphs and
degree-constraint graphs", IEICE Transactions on Information and Systems E96-D(11) (2013),
2327-2332, doi:10.1587/transinf.E96.D.2327, Theorem 2 (conference version: "On minimum feedback
vertex sets in graphs", Third International Conference on Networking and Computing (ICNC 2012),
429-434, doi:10.1109/ICNC.2012.81).
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetBipartiteDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetBipartitePlanar

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet

/-- Well-formedness of an instance: a well-formed FEEDBACK VERTEX SET on bipartite graphs
instance (a simple edge list whose graph is bipartite) whose graph is also planar. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSetBipartite.WellFormed i ∧ (Graph i).IsPlanar

open Classical in
/-- FEEDBACK VERTEX SET on planar bipartite graphs as a decision problem over bitstrings. -/
noncomputable def feedbackVertexSetBipartitePlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetBipartitePlanar
