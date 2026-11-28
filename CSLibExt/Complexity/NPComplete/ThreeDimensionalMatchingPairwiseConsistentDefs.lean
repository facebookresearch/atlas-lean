/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-DIMENSIONAL MATCHING for pairwise consistent triples: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP1] 3-DIMENSIONAL MATCHING, comment,
and the transformation from 3SAT in Section 3.1.2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ThreeDimensionalMatchingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatchingPairwiseConsistent



open ThreeDimensionalMatching (ThreeDimensionalMatchingInstance)

/-- Pairwise consistency of the triples: whenever `(a, b, w)`, `(a, x, c)` and `(y, b, c)` are
triples, so is `(a, b, c)`. -/
def PairwiseConsistent (M : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ t₁ ∈ M, ∀ t₂ ∈ M, ∀ t₃ ∈ M, t₁.1 = t₂.1 → t₁.2.1 = t₃.2.1 → t₂.2.2 = t₃.2.2 →
    (t₁.1, t₁.2.1, t₂.2.2) ∈ M

/-- Well-formedness of an instance: a well-formed 3-DIMENSIONAL MATCHING instance whose triples
are pairwise consistent. -/
def WellFormed (i : ThreeDimensionalMatchingInstance) : Prop :=
  ThreeDimensionalMatching.WellFormed i ∧ PairwiseConsistent i.2

open Classical in
/-- 3-DIMENSIONAL MATCHING for pairwise consistent triples as a decision problem over
bitstrings. -/
noncomputable def threeDimensionalMatchingPairwiseConsistentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeDimensionalMatchingInstance) x with
  | some i => decide (WellFormed i ∧ ThreeDimensionalMatching.ThreeDimensionalMatchingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatchingPairwiseConsistent
