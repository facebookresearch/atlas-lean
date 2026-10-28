/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthFinalPairQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSelectedOctadNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortQFinite
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMasks

/-! Selected genuine original short coordinates and their complete physical coefficient witnesses.
  -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The selected actual original short labels, in the fixed physical witness order. -/
def generatedTwelfthQSupportIndex : Fin 23 → GriessShortIndex :=
  ![
    Sum.inl (0, 0),
    Sum.inl (1, 0),
    Sum.inl (0, 1),
    Sum.inl (0, 2),
    Sum.inl (0, 15),
    Sum.inl (0, 16),
    Sum.inl (0, 17),
    Sum.inl (0, 86),
    Sum.inl (0, 101),
    Sum.inr (Sum.inl (508, 0)),
    Sum.inr (Sum.inl (90, 4)),
    Sum.inr (Sum.inl (4, 3)),
    Sum.inr (Sum.inl (54, 4)),
    Sum.inr (Sum.inl (91, 0)),
    Sum.inr (Sum.inl (94, 0)),
    Sum.inr (Sum.inl (94, 3)),
    Sum.inr (Sum.inl (293, 0)),
    Sum.inr (Sum.inl (293, 2)),
    Sum.inr (Sum.inl (105, 0)),
    Sum.inr (Sum.inl (252, 0)),
    Sum.inr (Sum.inl (275, 0)),
    Sum.inr (Sum.inl (659, 1)),
    Sum.inr (Sum.inl (736, 0))
  ]

/-- The signed original coefficients, all normalized by the actual denominator 128. -/
def generatedTwelfthQSupportNumerator : Fin 23 → ℤ :=
  ![-8, 8, -8, -8, 8, -8, -8, -8, 8, -8, 8, -8, -8, -8, 8, -8, -4, 4, 4, -12, -4, -4, -4]

/-- Original hyperbolic quotient masks for the selected preferred short lifts. -/
def generatedTwelfthQSupportMask : Fin 23 → ℕ :=
  ![6291456, 6293504, 5242880, 7340032, 4239360, 2011136, 3780608, 4718592, 32768, 47108, 1321136,
      169993, 4700265, 4817075, 5120185, 4860089, 6997336, 4558168, 7585997, 62511, 4728095,
      8103002, 7147152]

set_option maxHeartbeats 64000000 in
-- Bind every finite physical quotient bit to the complete original preferred lift.
/-- Every selected original preferred lift has exactly the stated original quotient mask. -/
theorem generatedTwelfth_Q_support_mask_actual : ∀ j : Fin 23, ∀ i : Fin 24,
    Multiplicative.toAdd
      (generatedAxisGlobalShortQFinite (generatedTwelfthQSupportIndex j)).base i =
      monsterCo1GeometryBinaryMaskDecode (generatedTwelfthQSupportMask j) i := by
  decide +kernel

/-- Every selected signed numerator is genuinely nonzero. -/
theorem generatedTwelfth_Q_support_numerator_ne_zero (j : Fin 23) :
    generatedTwelfthQSupportNumerator j ≠ 0 := by
  revert j
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 0. -/
theorem generatedTwelfthQSupportCoefficient00 :
    generatedTwelfthFinalPairQ 0 0 = (-8 : ℚ) / 128 := by
  rw [generatedTwelfthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 1. -/
theorem generatedTwelfthQSupportCoefficient01 :
    generatedTwelfthFinalPairQ 1 0 = (8 : ℚ) / 128 := by
  rw [generatedTwelfthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 2. -/
theorem generatedTwelfthQSupportCoefficient02 :
    generatedTwelfthFinalPairQ 0 1 = (-8 : ℚ) / 128 := by
  rw [generatedTwelfthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 3. -/
theorem generatedTwelfthQSupportCoefficient03 :
    generatedTwelfthFinalPairQ 0 2 = (-8 : ℚ) / 128 := by
  rw [generatedTwelfthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 4. -/
theorem generatedTwelfthQSupportCoefficient04 :
    generatedTwelfthFinalPairQ 0 15 = (8 : ℚ) / 128 := by
  rw [generatedTwelfthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 5. -/
theorem generatedTwelfthQSupportCoefficient05 :
    generatedTwelfthFinalPairQ 0 16 = (-8 : ℚ) / 128 := by
  rw [generatedTwelfthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 6. -/
theorem generatedTwelfthQSupportCoefficient06 :
    generatedTwelfthFinalPairQ 0 17 = (-8 : ℚ) / 128 := by
  rw [generatedTwelfthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 7. -/
theorem generatedTwelfthQSupportCoefficient07 :
    generatedTwelfthFinalPairQ 0 86 = (-8 : ℚ) / 128 := by
  rw [generatedTwelfthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 8. -/
theorem generatedTwelfthQSupportCoefficient08 :
    generatedTwelfthFinalPairQ 0 101 = (8 : ℚ) / 128 := by
  rw [generatedTwelfthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 9. -/
theorem generatedTwelfthQSupportCoefficient09 :
    generatedTwelfthSelectedOctadNumerator 0 0 = -8 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 10. -/
theorem generatedTwelfthQSupportCoefficient10 :
    generatedTwelfthSelectedOctadNumerator 1 4 = 8 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 11. -/
theorem generatedTwelfthQSupportCoefficient11 :
    generatedTwelfthSelectedOctadNumerator 2 3 = -8 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 12. -/
theorem generatedTwelfthQSupportCoefficient12 :
    generatedTwelfthSelectedOctadNumerator 3 4 = -8 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 13. -/
theorem generatedTwelfthQSupportCoefficient13 :
    generatedTwelfthSelectedOctadNumerator 4 0 = -8 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 14. -/
theorem generatedTwelfthQSupportCoefficient14 :
    generatedTwelfthSelectedOctadNumerator 5 0 = 8 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 15. -/
theorem generatedTwelfthQSupportCoefficient15 :
    generatedTwelfthSelectedOctadNumerator 5 3 = -8 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 16. -/
theorem generatedTwelfthQSupportCoefficient16 :
    generatedTwelfthSelectedOctadNumerator 6 0 = -4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 17. -/
theorem generatedTwelfthQSupportCoefficient17 :
    generatedTwelfthSelectedOctadNumerator 6 2 = 4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 18. -/
theorem generatedTwelfthQSupportCoefficient18 :
    generatedTwelfthSelectedOctadNumerator 7 0 = 4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 19. -/
theorem generatedTwelfthQSupportCoefficient19 :
    generatedTwelfthSelectedOctadNumerator 8 0 = -12 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 20. -/
theorem generatedTwelfthQSupportCoefficient20 :
    generatedTwelfthSelectedOctadNumerator 9 0 = -4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 21. -/
theorem generatedTwelfthQSupportCoefficient21 :
    generatedTwelfthSelectedOctadNumerator 10 1 = -4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 22. -/
theorem generatedTwelfthQSupportCoefficient22 :
    generatedTwelfthSelectedOctadNumerator 11 0 = -4 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
