/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthFinalPairQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthSelectedOctadNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortQFinite
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMasks

/-! Selected genuine original short coordinates and their complete physical coefficient witnesses.
  -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The selected actual original short labels, in the fixed physical witness order. -/
def generatedTenthQSupportIndex : Fin 23 → GriessShortIndex :=
  ![
    Sum.inl (0, 2),
    Sum.inl (1, 2),
    Sum.inl (0, 3),
    Sum.inl (0, 4),
    Sum.inl (0, 5),
    Sum.inl (0, 6),
    Sum.inl (0, 8),
    Sum.inl (0, 9),
    Sum.inl (0, 11),
    Sum.inl (0, 12),
    Sum.inl (0, 17),
    Sum.inl (0, 98),
    Sum.inr (Sum.inl (480, 1)),
    Sum.inr (Sum.inl (455, 1)),
    Sum.inr (Sum.inl (8, 2)),
    Sum.inr (Sum.inl (546, 0)),
    Sum.inr (Sum.inl (162, 0)),
    Sum.inr (Sum.inl (616, 0)),
    Sum.inr (Sum.inl (610, 0)),
    Sum.inr (Sum.inl (609, 1)),
    Sum.inr (Sum.inl (618, 0)),
    Sum.inr (Sum.inl (646, 2)),
    Sum.inr (Sum.inl (681, 0))
  ]

/-- The signed original coefficients, all normalized by the actual denominator 128. -/
def generatedTenthQSupportNumerator : Fin 23 → ℤ :=
  ![4, 12, -4, -4, 4, -4, 4, 4, 4, -4, -4, 8, 4, 8, -8, 4, 4, -4, -12, 4, 4, -4, -4]

/-- Original hyperbolic quotient masks for the selected preferred short lifts. -/
def generatedTenthQSupportMask : Fin 23 → ℕ :=
  ![7340032, 7342080, 4255744, 585728, 323584, 847872, 188416, 122880, 4247552, 2805760, 3780608,
      6176768, 638895, 245599, 6096909, 7170511, 4297152, 7089028, 7973711, 1856328, 7760783,
      3126320, 1105056]

set_option maxHeartbeats 64000000 in
-- Bind every finite physical quotient bit to the complete original preferred lift.
/-- Every selected original preferred lift has exactly the stated original quotient mask. -/
theorem generatedTenth_Q_support_mask_actual : ∀ j : Fin 23, ∀ i : Fin 24,
    Multiplicative.toAdd
      (generatedAxisGlobalShortQFinite (generatedTenthQSupportIndex j)).base i =
      monsterCo1GeometryBinaryMaskDecode (generatedTenthQSupportMask j) i := by
  decide +kernel

/-- Every selected signed numerator is genuinely nonzero. -/
theorem generatedTenth_Q_support_numerator_ne_zero (j : Fin 23) :
    generatedTenthQSupportNumerator j ≠ 0 := by
  revert j
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 0. -/
theorem generatedTenthQSupportCoefficient00 :
    generatedTenthFinalPairQ 0 2 = (4 : ℚ) / 128 := by
  rw [generatedTenthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 1. -/
theorem generatedTenthQSupportCoefficient01 :
    generatedTenthFinalPairQ 1 2 = (12 : ℚ) / 128 := by
  rw [generatedTenthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 2. -/
theorem generatedTenthQSupportCoefficient02 :
    generatedTenthFinalPairQ 0 3 = (-4 : ℚ) / 128 := by
  rw [generatedTenthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 3. -/
theorem generatedTenthQSupportCoefficient03 :
    generatedTenthFinalPairQ 0 4 = (-4 : ℚ) / 128 := by
  rw [generatedTenthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 4. -/
theorem generatedTenthQSupportCoefficient04 :
    generatedTenthFinalPairQ 0 5 = (4 : ℚ) / 128 := by
  rw [generatedTenthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 5. -/
theorem generatedTenthQSupportCoefficient05 :
    generatedTenthFinalPairQ 0 6 = (-4 : ℚ) / 128 := by
  rw [generatedTenthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 6. -/
theorem generatedTenthQSupportCoefficient06 :
    generatedTenthFinalPairQ 0 8 = (4 : ℚ) / 128 := by
  rw [generatedTenthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 7. -/
theorem generatedTenthQSupportCoefficient07 :
    generatedTenthFinalPairQ 0 9 = (4 : ℚ) / 128 := by
  rw [generatedTenthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 8. -/
theorem generatedTenthQSupportCoefficient08 :
    generatedTenthFinalPairQ 0 11 = (4 : ℚ) / 128 := by
  rw [generatedTenthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 9. -/
theorem generatedTenthQSupportCoefficient09 :
    generatedTenthFinalPairQ 0 12 = (-4 : ℚ) / 128 := by
  rw [generatedTenthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 10. -/
theorem generatedTenthQSupportCoefficient10 :
    generatedTenthFinalPairQ 0 17 = (-4 : ℚ) / 128 := by
  rw [generatedTenthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 11. -/
theorem generatedTenthQSupportCoefficient11 :
    generatedTenthFinalPairQ 0 98 = (8 : ℚ) / 128 := by
  rw [generatedTenthFinalPairQ, ← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 12. -/
theorem generatedTenthQSupportCoefficient12 :
    generatedTenthSelectedOctadNumerator 0 1 = 4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 13. -/
theorem generatedTenthQSupportCoefficient13 :
    generatedTenthSelectedOctadNumerator 1 1 = 8 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 14. -/
theorem generatedTenthQSupportCoefficient14 :
    generatedTenthSelectedOctadNumerator 2 2 = -8 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 15. -/
theorem generatedTenthQSupportCoefficient15 :
    generatedTenthSelectedOctadNumerator 3 0 = 4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 16. -/
theorem generatedTenthQSupportCoefficient16 :
    generatedTenthSelectedOctadNumerator 4 0 = 4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 17. -/
theorem generatedTenthQSupportCoefficient17 :
    generatedTenthSelectedOctadNumerator 5 0 = -4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 18. -/
theorem generatedTenthQSupportCoefficient18 :
    generatedTenthSelectedOctadNumerator 6 0 = -12 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 19. -/
theorem generatedTenthQSupportCoefficient19 :
    generatedTenthSelectedOctadNumerator 7 1 = 4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 20. -/
theorem generatedTenthQSupportCoefficient20 :
    generatedTenthSelectedOctadNumerator 8 0 = 4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 21. -/
theorem generatedTenthQSupportCoefficient21 :
    generatedTenthSelectedOctadNumerator 9 2 = -4 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check the entire actual original source formula for this signed coordinate.
/-- Complete original coefficient computation for selected physical witness 22. -/
theorem generatedTenthQSupportCoefficient22 :
    generatedTenthSelectedOctadNumerator 10 0 = -4 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
