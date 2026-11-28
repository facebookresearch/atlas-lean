/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on bipartite planar graphs of maximum degree 4: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET (the parent
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_1153` (bipartite ∩
maximum degree 4 ∩ planar), problem Feedback vertex set: NP-complete (reference note 1593, V. B.
Le: "Feedback vertex set is NP-complete for planar graph of maximum degree 4. By subdividing each
edge by one new vertex, it easily follows that feedback vertex set is also NP-complete on
bipartite planar graphs of maximum degree 4").
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetPlanarMaxDegreeFourDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetBipartitePlanarMaxDegreeFour

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
  (FeedbackVertexSetInstance Graph FeedbackVertexSetFeasible)

/-- Well-formedness of an instance: a well-formed instance of FEEDBACK VERTEX SET on planar
graphs of maximum degree 4 whose graph is bipartite, with `0 < K ≤ n`. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSetPlanarMaxDegreeFour.WellFormed i ∧ (Graph i).IsBipartite ∧ 0 < i.2.2 ∧
    i.2.2 ≤ i.1

open Classical in
/-- FEEDBACK VERTEX SET on bipartite planar graphs of maximum degree 4 as a decision problem over
bitstrings. -/
noncomputable def feedbackVertexSetBipartitePlanarMaxDegreeFourDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetBipartitePlanarMaxDegreeFour
