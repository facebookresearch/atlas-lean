/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK ARC SET on edge digraphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT8] FEEDBACK ARC SET, comment on
p. 192 ("for edge digraphs [Gavril, 1977a]");
F. Gavril, "Some NP-complete problems on graphs", Proc. 11th Conference on Information Sciences
and Systems, Johns Hopkins University, Baltimore, MD (1977), 91-95;
F. Harary and R. Z. Norman, "Some properties of line digraphs", Rendiconti del Circolo
Matematico di Palermo 9 (1960), 161-168, doi:10.1007/BF02854581 (edge digraphs).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FeedbackArcSetDefs
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetEdgeDigraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackArcSetEdgeDigraph

open MetaMathlibExt.Complexity.NPComplete.FeedbackArcSet
  (FeedbackArcSetInstance FeedbackArcSetFeasible)
open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetEdgeDigraph (IsEdgeDigraph)

/-- Well-formedness of an instance: a well-formed FEEDBACK ARC SET instance whose digraph is an
edge digraph, with `0 < K ≤ |A|`. -/
def WellFormed (i : FeedbackArcSetInstance) : Prop :=
  FeedbackArcSet.WellFormed i ∧ IsEdgeDigraph i.1 i.2.1 ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

open Classical in
/-- FEEDBACK ARC SET on edge digraphs as a decision problem over bitstrings. -/
noncomputable def feedbackArcSetEdgeDigraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeedbackArcSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackArcSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackArcSetEdgeDigraph
