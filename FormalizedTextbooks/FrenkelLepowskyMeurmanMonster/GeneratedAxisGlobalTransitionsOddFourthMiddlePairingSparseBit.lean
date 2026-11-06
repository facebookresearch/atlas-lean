/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingBit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonSparseBitFrames

/-! The entire actual original finite pairing with proved zero-input spin phase guards. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false

/-- All original middle inverse short terms, with complete zero-input phase guards. -/
def generatedAxisGlobalOddFourthMiddleShortSparseBitQ (k : Fin 4) :
    GeneratedAxisGlobalCanonicalFourthMiddleShortIndex → ℚ
  | Sum.inl j =>
      let d := (generatedFourthOddRootOutputData j).1
      let i := (generatedFourthOddRootOutputData j).2
      (if (golayEncodedMask d.val).testBit i.val then -1 else 1) *
        (generatedAxisGlobalOddFourthSparseBitFrameTensor k (generatedAxisGlobalOddFourthOutgoingTensor k)
          ⟨d.val, by omega⟩ i -
        generatedAxisGlobalOddFourthSparseBitFrameTensor k (generatedAxisGlobalOddFourthOutgoingTensor k)
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


/-- Every guarded original inverse short coefficient equals the complete certified bit coefficient. -/
theorem generatedAxisGlobalOddFourthMiddleShortSparseBitQ_eq (k : Fin 4)
    (p : GeneratedAxisGlobalCanonicalFourthMiddleShortIndex) :
    generatedAxisGlobalOddFourthMiddleShortSparseBitQ k p = generatedAxisGlobalOddFourthMiddleShortBitQ k p := by
  rcases p with j | (j | ⟨s,p⟩)
  · simp only [generatedAxisGlobalOddFourthMiddleShortSparseBitQ, generatedAxisGlobalOddFourthMiddleShortBitQ,
      generatedAxisGlobalOddFourthSparseBitFrameTensor_eq]
  · rfl
  · rfl

/-- The complete original finite pairing with only genuine nonzero incoming spin phases evaluated. -/
def generatedAxisGlobalOddFourthMiddlePairingSparseBitQ (k : Fin 4) : ℚ :=
  (∑ i : Fin 24, ∑ j : Fin 24,
    if generatedAxisGlobalCanonicalFourthMiddleMatrixQ i j = 0 then 0 else
      generatedAxisGlobalOddFourthMiddleMatrixBitQ k i j *
        generatedAxisGlobalCanonicalFourthMiddleMatrixQ i j) +
  (∑ p : GeneratedAxisGlobalCanonicalFourthMiddleShortIndex,
    if generatedAxisGlobalOddFourthMiddleCoefficientBitQ p = 0 then 0 else
      generatedAxisGlobalOddFourthMiddleCoefficientBitQ p *
        generatedAxisGlobalOddFourthMiddleShortSparseBitQ k p)

/-- The entire guarded finite expression is the previously certified complete original bit pairing. -/
theorem generatedAxisGlobalOddFourthMiddlePairingSparseBitQ_eq (k : Fin 4) :
    generatedAxisGlobalOddFourthMiddlePairingSparseBitQ k = generatedAxisGlobalOddFourthMiddlePairingBitQ k := by
  simp only [generatedAxisGlobalOddFourthMiddlePairingSparseBitQ, generatedAxisGlobalOddFourthMiddlePairingBitQ,
    generatedAxisGlobalOddFourthMiddleShortSparseBitQ_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
