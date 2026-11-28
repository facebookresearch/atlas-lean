/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on 2-subdivision graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), pp. 191-192, problem [GT7] FEEDBACK VERTEX
SET, comment: "The corresponding problem for undirected graphs is also NP-complete";
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_472`
(2-subdivision, https://www.graphclasses.org/classes/gc_472.html), problem Feedback vertex set:
NP-complete, with its note 1648 (communicated by P. Irzhavsky): the 2-subdivision of a graph
has a feedback vertex set of size `k` iff the graph does.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetDefs
public import CSLibExt.Complexity.NPComplete.MinimumCutLinearArrangementTwoSubdivisionPlanarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetTwoSubdivision

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
  (FeedbackVertexSetInstance Graph FeedbackVertexSetFeasible)
open MinimumCutLinearArrangementTwoSubdivisionPlanar (IsTwoSubdivision)

/-- Well-formedness of an instance: a well-formed FEEDBACK VERTEX SET instance with
`0 < K ≤ |V|` whose graph is a 2-subdivision. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ IsTwoSubdivision (Graph i)

open Classical in
/-- FEEDBACK VERTEX SET on 2-subdivision graphs as a decision problem over bitstrings. -/
noncomputable def feedbackVertexSetTwoSubdivisionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetTwoSubdivision
