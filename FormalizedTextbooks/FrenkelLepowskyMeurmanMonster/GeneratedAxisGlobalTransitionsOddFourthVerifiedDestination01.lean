/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingBit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingBoundedCheck01

/-! One complete genuine original signed triality vector is identified without pending comparisons. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- This entire genuine original transition vector has an actual canonical Fourth transporter. -/
theorem generatedAxisGlobalOddRoot02_negative_fourth_destination_verified :
    ∃ h : H, sExtra.symm (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 2) generatedOddAxis) =
      rhoLocal h generatedFourthAxis := by
  have hp : griessForm (generatedAxisGlobalOddFourthMiddleComparison 1)
      generatedAxisGlobalCanonicalFourthMiddleAxis = 128 := by
    rw [generatedAxisGlobalOddFourthMiddlePairingQ_actual,
      ← generatedAxisGlobalOddFourthMiddlePairingFastQ_eq 1
        (generatedAxisGlobalOddFourthSelectedShortQ_unconditional 1),
      ← generatedAxisGlobalOddFourthMiddlePairingBitQ_eq,
      generatedAxisGlobalOddFourthMiddlePairingBoundedCheck01]
    norm_num
  have hf := generatedAxisGlobalOddFourthDestination_of_pairing 1 hp
  have ht : (generatedAxisGlobalOddFourthComparisonAction 1).val generatedOddAxis =
      rhoLocal ((generatedAxisGlobalOddFourthComparisonLocal 1)⁻¹) generatedFourthAxis := by
    have h := congrArg (rhoLocal (generatedAxisGlobalOddFourthComparisonLocal 1)).symm hf
    rw [LinearEquiv.symm_apply_apply] at h
    rw [map_inv]
    exact h
  exact ⟨(generatedAxisGlobalOddFourthComparisonLocal 1)⁻¹,ht⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
