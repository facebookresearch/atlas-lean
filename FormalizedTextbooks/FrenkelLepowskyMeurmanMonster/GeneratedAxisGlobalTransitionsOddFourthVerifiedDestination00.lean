/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingBit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingBoundedCheck00

/-! One complete genuine original signed triality vector is identified without pending comparisons. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- This entire genuine original transition vector has an actual canonical Fourth transporter. -/
theorem generatedAxisGlobalOddRoot02_positive_fourth_destination_verified :
    ∃ h : H, sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 2) generatedOddAxis) =
      rhoLocal h generatedFourthAxis := by
  have hp : griessForm (generatedAxisGlobalOddFourthMiddleComparison 0)
      generatedAxisGlobalCanonicalFourthMiddleAxis = 128 := by
    rw [generatedAxisGlobalOddFourthMiddlePairingQ_actual,
      ← generatedAxisGlobalOddFourthMiddlePairingFastQ_eq 0
        (generatedAxisGlobalOddFourthSelectedShortQ_unconditional 0),
      ← generatedAxisGlobalOddFourthMiddlePairingBitQ_eq,
      generatedAxisGlobalOddFourthMiddlePairingBoundedCheck00]
    norm_num
  have hf := generatedAxisGlobalOddFourthDestination_of_pairing 0 hp
  have ht : (generatedAxisGlobalOddFourthComparisonAction 0).val generatedOddAxis =
      rhoLocal ((generatedAxisGlobalOddFourthComparisonLocal 0)⁻¹) generatedFourthAxis := by
    have h := congrArg (rhoLocal (generatedAxisGlobalOddFourthComparisonLocal 0)).symm hf
    rw [LinearEquiv.symm_apply_apply] at h
    rw [map_inv]
    exact h
  exact ⟨(generatedAxisGlobalOddFourthComparisonLocal 0)⁻¹,ht⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
