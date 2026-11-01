/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingBit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingBoundedCheck00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingBoundedCheck01

/-! The whole original signed root-three transition vectors have actual canonical Fifth destinations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Every original matrix, preferred short and tensor term contributes to the actual pairing. -/
theorem generatedAxisGlobalOddFifthMiddlePairingBitQ_actual (k : Fin 2) :
    griessForm (generatedAxisGlobalOddFifthMiddleComparison k)
      generatedAxisGlobalCanonicalFifthMiddleAxis =
        (generatedAxisGlobalOddFifthMiddlePairingBitQ k : ℝ) := by
  rw [generatedAxisGlobalOddFifthMiddlePairingQ_actual,
    ← generatedAxisGlobalOddFifthMiddlePairingFastQ_eq k
      (generatedAxisGlobalOddFifthSelectedShortQ_unconditional k),
    ← generatedAxisGlobalOddFifthMiddlePairingBitQ_eq]

/-- Both original complete pairings are assembled from every kernel-checked finite packet. -/
theorem generatedAxisGlobalOddFifthMiddlePairingBitQ_checked (k : Fin 2) :
    generatedAxisGlobalOddFifthMiddlePairingBitQ k = 128 := by
  fin_cases k
  · exact generatedAxisGlobalOddFifthMiddlePairingBoundedCheck00
  · exact generatedAxisGlobalOddFifthMiddlePairingBoundedCheck01

/-- The complete genuine framed transition vector equals the original canonical Fifth axis. -/
theorem generatedAxisGlobalOddFifth_full_destination (k : Fin 2) :
    rhoLocal (generatedAxisGlobalOddFifthComparisonLocal k)
      ((generatedAxisGlobalOddFifthComparisonAction k).val generatedOddAxis) = generatedFifthAxis := by
  apply generatedAxisGlobalOddFifthDestination_of_pairing
  rw [generatedAxisGlobalOddFifthMiddlePairingBitQ_actual,
    generatedAxisGlobalOddFifthMiddlePairingBitQ_checked]
  norm_num

/-- The inverse of the complete original frame is a genuine whole-vector transporter. -/
theorem generatedAxisGlobalOddFifth_transporter (k : Fin 2) :
    (generatedAxisGlobalOddFifthComparisonAction k).val generatedOddAxis =
      rhoLocal ((generatedAxisGlobalOddFifthComparisonLocal k)⁻¹) generatedFifthAxis := by
  have h := congrArg (rhoLocal (generatedAxisGlobalOddFifthComparisonLocal k)).symm
    (generatedAxisGlobalOddFifth_full_destination k)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [map_inv]
  exact h

/-- Positive genuine original root-three triality has an actual canonical Fifth destination. -/
theorem generatedAxisGlobalOddRoot03_positive_fifth_destination :
    ∃ h : H, sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 3) generatedOddAxis) =
      rhoLocal h generatedFifthAxis :=
  ⟨(generatedAxisGlobalOddFifthComparisonLocal 0)⁻¹, generatedAxisGlobalOddFifth_transporter 0⟩

/-- Negative genuine original root-three triality has an actual canonical Fifth destination. -/
theorem generatedAxisGlobalOddRoot03_negative_fifth_destination :
    ∃ h : H, sExtra.symm (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 3) generatedOddAxis) =
      rhoLocal h generatedFifthAxis :=
  ⟨(generatedAxisGlobalOddFifthComparisonLocal 1)⁻¹, generatedAxisGlobalOddFifth_transporter 1⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
