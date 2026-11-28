/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on planar graphs: definitions

Source:
A. Munaro, "On line graphs of subcubic triangle-free graphs", Discrete Mathematics 340(6)
(2017), 1210-1226, doi:10.1016/j.disc.2017.01.006, introduction ("Feedback Vertex Set becomes
NP-hard for graphs with maximum degree 4, even if restricted to be planar, as shown by
Speckenmeyer", citing the two works below);
E. Speckenmeyer, *Untersuchungen zum Feedback Vertex Set Problem in ungerichteten Graphen*,
Ph.D. thesis, Universität Paderborn (1983) (not available here);
E. Speckenmeyer, "On feedback vertex sets and nonseparating independent sets in cubic graphs",
Journal of Graph Theory 12(3) (1988), 405-412, doi:10.1002/jgt.3190120311;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET (comment: "The
corresponding problem for undirected graphs is also NP-complete");
ISGCI (https://www.graphclasses.org/classes/gc_43.html), class "planar", problem "Feedback
vertex set": NP-complete.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPlanar

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
  (FeedbackVertexSetInstance Graph FeedbackVertexSetFeasible)

/-- Well-formedness of an instance: a well-formed FEEDBACK VERTEX SET instance (a simple edge
list on `Fin n`) whose graph is planar, with `0 < K ≤ n`. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSet.WellFormed i ∧ (Graph i).IsPlanar ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- FEEDBACK VERTEX SET on planar graphs as a decision problem over bitstrings. -/
noncomputable def feedbackVertexSetPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPlanar
