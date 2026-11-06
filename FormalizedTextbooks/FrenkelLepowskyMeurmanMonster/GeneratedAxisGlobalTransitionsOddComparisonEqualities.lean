/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRationalBindings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonPairingCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonActions

/-! Complete original source-vector equality of three genuine odd-axis transition outputs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The entire rational outgoing packet is the exact original actual source transition. -/
theorem generatedAxisGlobalOddComparisonTransitionPacket_actual (k : Fin 3) :
    griessConwayEncode ((generatedAxisGlobalOddComparisonAction k).val generatedOddAxis) =
      generatedAxisGlobalRationalPacketReal (generatedAxisGlobalOddComparisonTransitionPacket k) := by
  fin_cases k
  · change griessConwayEncode
      (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 0) generatedOddAxis)) = _
    exact generatedAxisGlobalRationalTriality_of_actual _ _
      (generatedAxisGlobalOddSparseRootPacket_actual 0)
  · change griessConwayEncode
      (sExtra.symm (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 0) generatedOddAxis)) = _
    exact generatedAxisGlobalRationalInverse_actual _ _
      (generatedAxisGlobalOddSparseRootPacket_actual 0)
  · change griessConwayEncode
      (sExtra.symm (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis)) = _
    exact generatedAxisGlobalRationalInverse_actual _ _
      (generatedAxisGlobalOddSparseRootPacket_actual 1)

/-- The complete original source pairing equals 128 across all three constituents. -/
theorem generatedAxisGlobalOddComparison_full_pairing (k : Fin 3) :
    griessForm ((generatedAxisGlobalOddComparisonAction k).val generatedOddAxis)
      (rhoLocal (generatedAxisGlobalOddComparisonLocal k) generatedOddAxis) = 128 := by
  have hd : 0 < generatedAxisGlobalOddRationalComparisonDenominator k := by
    fin_cases k <;> decide
  have h := generatedAxisGlobalRationalSparsePairing_actual
    ((generatedAxisGlobalOddComparisonAction k).val generatedOddAxis)
    (rhoLocal (generatedAxisGlobalOddComparisonLocal k) generatedOddAxis)
    (generatedAxisGlobalOddComparisonTransitionPacket k)
    (generatedAxisGlobalOddComparisonMatrixQ k)
    (generatedAxisGlobalOddSparseCoefficient ⟨k.val + 2, by omega⟩)
    (generatedAxisGlobalOddSparseLabel ⟨k.val + 2, by omega⟩)
    (generatedAxisGlobalOddRationalComparisonSpin k)
    (generatedAxisGlobalOddRationalComparisonSpatial k)
    (generatedAxisGlobalOddRationalComparisonDenominator k) hd
    (generatedAxisGlobalOddComparisonTransitionPacket_actual k)
    (generatedAxisGlobalOddComparisonMatrix_actual k)
    (generatedAxisGlobalOddRationalComparisonShort_actual k)
    (generatedAxisGlobalOddRationalComparisonTensor_actual k)
  change griessForm ((generatedAxisGlobalOddComparisonAction k).val generatedOddAxis)
      (rhoLocal (generatedAxisGlobalOddComparisonLocal k) generatedOddAxis) =
    (generatedAxisGlobalOddComparisonPairingQ k : ℝ) at h
  rw [generatedAxisGlobalOddComparisonPairing_certificate] at h
  simpa only [Rat.cast_ofNat] using h

/-- Every original coordinate of all three actual transition vectors equals its genuine local comparison. -/
theorem generatedAxisGlobalOddComparison_full_equality (k : Fin 3) :
    (generatedAxisGlobalOddComparisonAction k).val generatedOddAxis =
      rhoLocal (generatedAxisGlobalOddComparisonLocal k) generatedOddAxis :=
  generatedAxisGlobalOddComparison_eq_of_pairing k (generatedAxisGlobalOddComparison_full_pairing k)

/-- Original positive root-zero triality is the entire phase-preserving comparison-zero local image. -/
theorem generatedAxisGlobalOddRoot00_positive_comparison :
    sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 0) generatedOddAxis) =
      rhoLocal (generatedAxisGlobalOddComparisonLocal 0) generatedOddAxis := by
  exact generatedAxisGlobalOddComparison_full_equality 0

/-- Original inverse root-zero triality is the entire phase-preserving comparison-one local image. -/
theorem generatedAxisGlobalOddRoot00_negative_comparison :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 0) generatedOddAxis) =
      rhoLocal (generatedAxisGlobalOddComparisonLocal 1) generatedOddAxis := by
  exact generatedAxisGlobalOddComparison_full_equality 1

/-- Original inverse root-six triality is the entire phase-preserving comparison-two local image. -/
theorem generatedAxisGlobalOddRoot06_negative_comparison :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis) =
      rhoLocal (generatedAxisGlobalOddComparisonLocal 2) generatedOddAxis := by
  exact generatedAxisGlobalOddComparison_full_equality 2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
