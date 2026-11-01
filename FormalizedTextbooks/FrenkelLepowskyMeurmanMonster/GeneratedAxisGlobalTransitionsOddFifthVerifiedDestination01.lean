/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingBit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingBoundedCheck01

/-! One complete original signed root-three transition vector has an actual canonical Fifth destination. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- This entire genuine original root-three transition vector has an actual canonical Fifth transporter. -/
theorem generatedAxisGlobalOddRoot03_negative_fifth_destination_verified :
    ∃ h : H, sExtra.symm (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 3) generatedOddAxis) =
      rhoLocal h generatedFifthAxis := by
  have hp : griessForm (generatedAxisGlobalOddFifthMiddleComparison 1)
      generatedAxisGlobalCanonicalFifthMiddleAxis = 128 := by
    rw [generatedAxisGlobalOddFifthMiddlePairingQ_actual,
      ← generatedAxisGlobalOddFifthMiddlePairingFastQ_eq 1
        (generatedAxisGlobalOddFifthSelectedShortQ_unconditional 1),
      ← generatedAxisGlobalOddFifthMiddlePairingBitQ_eq,
      generatedAxisGlobalOddFifthMiddlePairingBoundedCheck01]
    norm_num
  have hf := generatedAxisGlobalOddFifthDestination_of_pairing 1 hp
  have ht : (generatedAxisGlobalOddFifthComparisonAction 1).val generatedOddAxis =
      rhoLocal ((generatedAxisGlobalOddFifthComparisonLocal 1)⁻¹) generatedFifthAxis := by
    have h := congrArg (rhoLocal (generatedAxisGlobalOddFifthComparisonLocal 1)).symm hf
    rw [LinearEquiv.symm_apply_apply] at h
    rw [map_inv]
    exact h
  exact ⟨(generatedAxisGlobalOddFifthComparisonLocal 1)⁻¹, ht⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
