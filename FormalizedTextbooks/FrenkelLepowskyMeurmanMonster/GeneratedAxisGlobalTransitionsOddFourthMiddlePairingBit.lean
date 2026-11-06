/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonBitFrames
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalSpatialMatrixWordSparse

/-! The entire original finite pairing with certified bit tensor evaluation and proven matrix zero guards. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Complete actual physical frame matrix with proven inverse-column zero guards. -/
def generatedAxisGlobalOddFourthFramedSparseMatrix (k : Fin 4) : Matrix (Fin 24) (Fin 24) ℚ :=
  generatedAxisGlobalRationalSpatialMatrixWordSparse (generatedAxisGlobalOddFourthComparisonLetters k)
    (generatedAxisGlobalOddFourthOutgoingPacket k).1

/-- The guarded complete physical matrix is the original whole actual frame matrix. -/
theorem generatedAxisGlobalOddFourthFramedSparseMatrix_eq (k : Fin 4) :
    generatedAxisGlobalOddFourthFramedSparseMatrix k = generatedAxisGlobalOddFourthFramedMatrix k :=
  generatedAxisGlobalRationalSpatialMatrixWordSparse_eq _ _

/-- Every needed inverse matrix coefficient, with only its original diagonal source matrix evaluated. -/
def generatedAxisGlobalOddFourthMiddleMatrixBitQ (k : Fin 4) (i j : Fin 24) : ℚ :=
  if i = j then generatedAxisGlobalOddFourthFramedSparseMatrix k i i else
    generatedAxisGlobalOddFourthMiddleMatrixFastQ k i j

/-- All actual middle inverse short terms retain their original selected coefficients and complete tensor signs. -/
def generatedAxisGlobalOddFourthMiddleShortBitQ (k : Fin 4) :
    GeneratedAxisGlobalCanonicalFourthMiddleShortIndex → ℚ
  | Sum.inl j =>
      let d := (generatedFourthOddRootOutputData j).1
      let i := (generatedFourthOddRootOutputData j).2
      (if (golayEncodedMask d.val).testBit i.val then -1 else 1) *
        (generatedAxisGlobalOddFourthBitFrameTensor k (generatedAxisGlobalOddFourthOutgoingTensor k)
          ⟨d.val, by omega⟩ i -
        generatedAxisGlobalOddFourthBitFrameTensor k (generatedAxisGlobalOddFourthOutgoingTensor k)
          ⟨d.val+2048, by omega⟩ i) / 2
  | Sum.inr (Sum.inl j) => generatedAxisGlobalOddFourthMiddleShortFastQ k (Sum.inr (Sum.inl j))
  | Sum.inr (Sum.inr (s,p)) =>
      if s = 0 then generatedAxisGlobalOddFourthFramedSparseMatrix k
          (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 +
        (generatedAxisGlobalOddFourthSelectedShortQ k (generatedAxisGlobalOddFourthSelectedPair 0 p) +
          generatedAxisGlobalOddFourthSelectedShortQ k (generatedAxisGlobalOddFourthSelectedPair 1 p)) / 2
      else generatedAxisGlobalOddFourthFramedSparseMatrix k
          (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 -
        (generatedAxisGlobalOddFourthSelectedShortQ k (generatedAxisGlobalOddFourthSelectedPair 0 p) +
          generatedAxisGlobalOddFourthSelectedShortQ k (generatedAxisGlobalOddFourthSelectedPair 1 p)) / 2

/-- Every original finite support coefficient, with its actual preferred pair evaluated in finite coordinates. -/
def generatedAxisGlobalOddFourthMiddleCoefficientBitQ :
    GeneratedAxisGlobalCanonicalFourthMiddleShortIndex → ℚ
  | Sum.inl j => generatedAxisGlobalCanonicalFourthMiddleShortCoefficient (Sum.inl j)
  | Sum.inr (Sum.inl j) => generatedAxisGlobalCanonicalFourthMiddleShortCoefficient (Sum.inr (Sum.inl j))
  | Sum.inr (Sum.inr (s,p)) => if s = 1 ∧ generatedAxisGlobalPairCoordinates p = (8,11) then -1 else 0

/-- Finite support coefficients are exactly the original complete actual coefficients. -/
theorem generatedAxisGlobalOddFourthMiddleCoefficientBitQ_eq
    (p : GeneratedAxisGlobalCanonicalFourthMiddleShortIndex) :
    generatedAxisGlobalOddFourthMiddleCoefficientBitQ p =
      generatedAxisGlobalCanonicalFourthMiddleShortCoefficient p := by
  rcases p with j | (j | ⟨s,p⟩)
  · rfl
  · rfl
  · change (if s = 1 ∧ generatedAxisGlobalPairCoordinates p = (8,11) then (-1 : ℚ) else 0) =
      (if s = 1 ∧ griessCoordinatePair p = (8,11) then -1 else 0)
    rw [generatedAxisGlobalPairCoordinates_actual]

/-- The whole original finite middle pairing with exact bit tensor formulas and proven zero matrix guards. -/
def generatedAxisGlobalOddFourthMiddlePairingBitQ (k : Fin 4) : ℚ :=
  (∑ i : Fin 24, ∑ j : Fin 24,
    if generatedAxisGlobalCanonicalFourthMiddleMatrixQ i j = 0 then 0 else
      generatedAxisGlobalOddFourthMiddleMatrixBitQ k i j *
        generatedAxisGlobalCanonicalFourthMiddleMatrixQ i j) +
  (∑ p : GeneratedAxisGlobalCanonicalFourthMiddleShortIndex,
    if generatedAxisGlobalOddFourthMiddleCoefficientBitQ p = 0 then 0 else
      generatedAxisGlobalOddFourthMiddleCoefficientBitQ p *
        generatedAxisGlobalOddFourthMiddleShortBitQ k p)

/-- Every bit inverse matrix coefficient is the exact original complete coefficient. -/
theorem generatedAxisGlobalOddFourthMiddleMatrixBitQ_eq (k : Fin 4) (i j : Fin 24) :
    generatedAxisGlobalOddFourthMiddleMatrixBitQ k i j =
      generatedAxisGlobalOddFourthMiddleMatrixFastQ k i j := by
  by_cases h : i = j
  · simp only [generatedAxisGlobalOddFourthMiddleMatrixBitQ, h, ↓reduceIte,
      generatedAxisGlobalOddFourthFramedSparseMatrix_eq, generatedAxisGlobalOddFourthMiddleMatrixFastQ]
  · simp only [generatedAxisGlobalOddFourthMiddleMatrixBitQ, h, ↓reduceIte]

/-- Every bit inverse short coefficient is the exact original complete coefficient. -/
theorem generatedAxisGlobalOddFourthMiddleShortBitQ_eq (k : Fin 4)
    (p : GeneratedAxisGlobalCanonicalFourthMiddleShortIndex) :
    generatedAxisGlobalOddFourthMiddleShortBitQ k p = generatedAxisGlobalOddFourthMiddleShortFastQ k p := by
  rcases p with j | (j | ⟨s,p⟩)
  · simp only [generatedAxisGlobalOddFourthMiddleShortBitQ, generatedAxisGlobalOddFourthMiddleShortFastQ,
      generatedAxisGlobalInverseShortQ, generatedFourthOddRootOutputLabel,
      generatedAxisGlobalOddFourthFramedPacket, generatedAxisGlobalOddFourthFramedTensor,
      generatedAxisGlobalSpinLabel_coeff, generatedAxisGlobalOddFourthBitFrameTensor_eq]
  · rfl
  · simp only [generatedAxisGlobalOddFourthMiddleShortBitQ, generatedAxisGlobalOddFourthMiddleShortFastQ,
      generatedAxisGlobalOddFourthFramedSparseMatrix_eq]

/-- The bit expression retains the complete original finite pairing, including all constituents. -/
theorem generatedAxisGlobalOddFourthMiddlePairingBitQ_eq (k : Fin 4) :
    generatedAxisGlobalOddFourthMiddlePairingBitQ k = generatedAxisGlobalOddFourthMiddlePairingFastQ k := by
  simp only [generatedAxisGlobalOddFourthMiddlePairingBitQ, generatedAxisGlobalOddFourthMiddlePairingFastQ,
    generatedAxisGlobalOddFourthMiddleMatrixBitQ_eq, generatedAxisGlobalOddFourthMiddleShortBitQ_eq,
    generatedAxisGlobalOddFourthMiddleCoefficientBitQ_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
