/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK ARC SET with total degree at most 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT8] FEEDBACK ARC SET, comment on
p. 192 ("Remains NP-complete for digraphs in which no vertex has total in-degree and out-degree
more than 3, and for edge digraphs [Gavril, 1977a]");
F. Gavril, "Some NP-complete problems on graphs", Proc. 11th Conference on Information Sciences
and Systems, Johns Hopkins University, Baltimore, MD (1977), 91-95.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FeedbackArcSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackArcSetDegreeThree

open MetaMathlibExt.Complexity.NPComplete.FeedbackArcSet
  (FeedbackArcSetInstance FeedbackArcSetFeasible)

/-- Well-formedness of an instance: a well-formed FEEDBACK ARC SET instance in which every
vertex has in-degree plus out-degree at most 3, with `0 < K ≤ |A|`. -/
def WellFormed (i : FeedbackArcSetInstance) : Prop :=
  FeedbackArcSet.WellFormed i ∧
    (∀ v : ℕ, i.2.1.countP (fun e => e.2 = v) + i.2.1.countP (fun e => e.1 = v) ≤ 3) ∧
      0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

open Classical in
/-- FEEDBACK ARC SET with total degree at most 3 as a decision problem over bitstrings. -/
noncomputable def feedbackArcSetDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeedbackArcSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackArcSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackArcSetDegreeThree
