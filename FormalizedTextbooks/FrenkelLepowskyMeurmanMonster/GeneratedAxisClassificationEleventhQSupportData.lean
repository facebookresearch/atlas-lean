/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhFinalPairQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhSelectedOctadNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortQFinite
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMasks

/-! Selected genuine original short coordinates and their complete physical coefficient witnesses.
  -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The selected actual original short labels, in the fixed physical witness order. -/
def generatedEleventhQSupportIndex : Fin 21 → GriessShortIndex :=
  ![
    Sum.inl (0, 0),
    Sum.inl (1, 0),
    Sum.inl (0, 1),
    Sum.inl (0, 2),
    Sum.inl (0, 3),
    Sum.inl (0, 4),
    Sum.inl (0, 5),
    Sum.inl (0, 15),
    Sum.inl (0, 16),
    Sum.inl (0, 17),
    Sum.inl (0, 19),
    Sum.inr (Sum.inl (236, 0)),
    Sum.inr (Sum.inl (508, 0)),
    Sum.inr (Sum.inl (6, 0)),
    Sum.inr (Sum.inl (235, 16)),
    Sum.inr (Sum.inl (230, 16)),
    Sum.inr (Sum.inl (233, 0)),
    Sum.inr (Sum.inl (243, 0)),
    Sum.inr (Sum.inl (13, 0)),
    Sum.inr (Sum.inl (194, 0)),
    Sum.inr (Sum.inl (455, 16))
  ]

/-- The signed original coefficients, all normalized by the actual denominator 128. -/
def generatedEleventhQSupportNumerator : Fin 21 → ℤ :=
  ![-12, -4, 4, 4, 4, -4, -4, 4, -4, 4, -4, -4, -4, -4, 4, 4, -4, 4, -4, -4, -12]

/-- Original hyperbolic quotient masks for the selected preferred short lifts. -/
def generatedEleventhQSupportMask : Fin 21 → ℕ :=
  ![6291456, 6293504, 5242880, 7340032, 4255744, 585728, 323584, 4239360, 2011136, 3780608,
      4222976, 1627019, 47108, 4210699, 3578758, 6683488, 3191662, 1356743, 7639062, 4272768,
      7429983]

set_option maxHeartbeats 64000000 in
-- Bind every finite physical quotient bit to the complete original preferred lift.
/-- Every selected original preferred lift has exactly the stated original quotient mask. -/
theorem generatedEleventh_Q_support_mask_actual : ∀ j : Fin 21, ∀ i : Fin 24,
    Multiplicative.toAdd
      (generatedAxisGlobalShortQFinite (generatedEleventhQSupportIndex j)).base i =
      monsterCo1GeometryBinaryMaskDecode (generatedEleventhQSupportMask j) i := by
  decide +kernel

/-- Every selected signed numerator is genuinely nonzero. -/
theorem generatedEleventh_Q_support_numerator_ne_zero (j : Fin 21) :
    generatedEleventhQSupportNumerator j ≠ 0 := by
  revert j
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 0. -/
theorem generatedEleventhQSupportCoefficient00 :
    generatedEleventhFinalPairQ 0 0 = (-12 : ℚ) / 128 := by
  rw [generatedEleventhFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 1. -/
theorem generatedEleventhQSupportCoefficient01 :
    generatedEleventhFinalPairQ 1 0 = (-4 : ℚ) / 128 := by
  rw [generatedEleventhFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 2. -/
theorem generatedEleventhQSupportCoefficient02 :
    generatedEleventhFinalPairQ 0 1 = (4 : ℚ) / 128 := by
  rw [generatedEleventhFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 3. -/
theorem generatedEleventhQSupportCoefficient03 :
    generatedEleventhFinalPairQ 0 2 = (4 : ℚ) / 128 := by
  rw [generatedEleventhFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 4. -/
theorem generatedEleventhQSupportCoefficient04 :
    generatedEleventhFinalPairQ 0 3 = (4 : ℚ) / 128 := by
  rw [generatedEleventhFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 5. -/
theorem generatedEleventhQSupportCoefficient05 :
    generatedEleventhFinalPairQ 0 4 = (-4 : ℚ) / 128 := by
  rw [generatedEleventhFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 6. -/
theorem generatedEleventhQSupportCoefficient06 :
    generatedEleventhFinalPairQ 0 5 = (-4 : ℚ) / 128 := by
  rw [generatedEleventhFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 7. -/
theorem generatedEleventhQSupportCoefficient07 :
    generatedEleventhFinalPairQ 0 15 = (4 : ℚ) / 128 := by
  rw [generatedEleventhFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 8. -/
theorem generatedEleventhQSupportCoefficient08 :
    generatedEleventhFinalPairQ 0 16 = (-4 : ℚ) / 128 := by
  rw [generatedEleventhFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 9. -/
theorem generatedEleventhQSupportCoefficient09 :
    generatedEleventhFinalPairQ 0 17 = (4 : ℚ) / 128 := by
  rw [generatedEleventhFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 10. -/
theorem generatedEleventhQSupportCoefficient10 :
    generatedEleventhFinalPairQ 0 19 = (-4 : ℚ) / 128 := by
  rw [generatedEleventhFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 11. -/
theorem generatedEleventhQSupportCoefficient11 :
    generatedEleventhSelectedOctadNumerator 0 0 = -4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 12. -/
theorem generatedEleventhQSupportCoefficient12 :
    generatedEleventhSelectedOctadNumerator 1 0 = -4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 13. -/
theorem generatedEleventhQSupportCoefficient13 :
    generatedEleventhSelectedOctadNumerator 2 0 = -4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 14. -/
theorem generatedEleventhQSupportCoefficient14 :
    generatedEleventhSelectedOctadNumerator 3 16 = 4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 15. -/
theorem generatedEleventhQSupportCoefficient15 :
    generatedEleventhSelectedOctadNumerator 4 16 = 4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 16. -/
theorem generatedEleventhQSupportCoefficient16 :
    generatedEleventhSelectedOctadNumerator 5 0 = -4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 17. -/
theorem generatedEleventhQSupportCoefficient17 :
    generatedEleventhSelectedOctadNumerator 6 0 = 4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 18. -/
theorem generatedEleventhQSupportCoefficient18 :
    generatedEleventhSelectedOctadNumerator 7 0 = -4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 19. -/
theorem generatedEleventhQSupportCoefficient19 :
    generatedEleventhSelectedOctadNumerator 8 0 = -4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 20. -/
theorem generatedEleventhQSupportCoefficient20 :
    generatedEleventhSelectedOctadNumerator 9 16 = -12 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
