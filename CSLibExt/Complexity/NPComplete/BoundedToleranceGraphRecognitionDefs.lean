/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED TOLERANCE GRAPH RECOGNITION: definitions

Source:
G. B. Mertzios, I. Sau and S. Zaks, "The recognition of tolerance and bounded tolerance graphs",
SIAM Journal on Computing 40 (2011), 1234-1257, doi:10.1137/090780328 (arXiv:1001.3251;
Section 1: the definitions of tolerance and bounded tolerance graphs used below, and "both
recognition problems are NP-complete", membership in NP citing Hayward and Shamir).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ToleranceGraphRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedToleranceGraphRecognition

open MetaMathlibExt.Complexity.NPComplete.ToleranceGraphRecognition
  (ToleranceGraphRecognitionInstance Graph IsToleranceRepresentation)

/-- The graph of the instance is a bounded tolerance graph: it has a tolerance representation
in which every tolerance is at most the length of its vertex's interval. -/
def BoundedToleranceGraphRecognitionFeasible (i : ToleranceGraphRecognitionInstance) : Prop :=
  ∃ l r t : Fin i.1 → ℝ, IsToleranceRepresentation (Graph i) l r t ∧ ∀ v, t v ≤ r v - l v

open Classical in
/-- BOUNDED TOLERANCE GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def boundedToleranceGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ToleranceGraphRecognitionInstance) x with
  | some i =>
    decide (ToleranceGraphRecognition.WellFormed i ∧ BoundedToleranceGraphRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BoundedToleranceGraphRecognition
