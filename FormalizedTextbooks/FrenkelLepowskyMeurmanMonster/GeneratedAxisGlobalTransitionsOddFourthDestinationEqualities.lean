/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingBit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingBitCheck00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingBitCheck01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingBitCheck02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingBitCheck03

/-! Complete genuine original signed root-two and root-four transition destinations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- The exact bit expression is the entire actual middle pairing after all original Q certificates. -/
theorem generatedAxisGlobalOddFourthMiddlePairingBitQ_actual (k : Fin 4) :
    griessForm (generatedAxisGlobalOddFourthMiddleComparison k)
      generatedAxisGlobalCanonicalFourthMiddleAxis =
        (generatedAxisGlobalOddFourthMiddlePairingBitQ k : ℝ) := by
  rw [generatedAxisGlobalOddFourthMiddlePairingQ_actual,
    ← generatedAxisGlobalOddFourthMiddlePairingFastQ_eq k
      (generatedAxisGlobalOddFourthSelectedShortQ_unconditional k),
    ← generatedAxisGlobalOddFourthMiddlePairingBitQ_eq]

/-- Every complete original numerical pairing is kernel checked. -/
theorem generatedAxisGlobalOddFourthMiddlePairingBitQ_checked (k : Fin 4) :
    generatedAxisGlobalOddFourthMiddlePairingBitQ k = 128 := by
  fin_cases k
  · exact generatedAxisGlobalOddFourthMiddlePairingBitCheck00
  · exact generatedAxisGlobalOddFourthMiddlePairingBitCheck01
  · exact generatedAxisGlobalOddFourthMiddlePairingBitCheck02
  · exact generatedAxisGlobalOddFourthMiddlePairingBitCheck03

/-- Each genuine whole outgoing axis is identified with the complete original canonical Fourth axis. -/
theorem generatedAxisGlobalOddFourth_full_destination (k : Fin 4) :
    rhoLocal (generatedAxisGlobalOddFourthComparisonLocal k)
      ((generatedAxisGlobalOddFourthComparisonAction k).val generatedOddAxis) = generatedFourthAxis := by
  apply generatedAxisGlobalOddFourthDestination_of_pairing
  rw [generatedAxisGlobalOddFourthMiddlePairingBitQ_actual,
    generatedAxisGlobalOddFourthMiddlePairingBitQ_checked]
  norm_num

/-- The original inverse of the complete genuine frame is an actual whole-axis transporter. -/
theorem generatedAxisGlobalOddFourth_transporter (k : Fin 4) :
    (generatedAxisGlobalOddFourthComparisonAction k).val generatedOddAxis =
      rhoLocal ((generatedAxisGlobalOddFourthComparisonLocal k)⁻¹) generatedFourthAxis := by
  have h := congrArg (rhoLocal (generatedAxisGlobalOddFourthComparisonLocal k)).symm
    (generatedAxisGlobalOddFourth_full_destination k)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [map_inv]
  exact h

/-- The actual positive original root-two transition has canonical Fourth destination. -/
theorem generatedAxisGlobalOddRoot02_positive_fourth_destination :
    ∃ h : H, sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 2) generatedOddAxis) =
      rhoLocal h generatedFourthAxis :=
  ⟨(generatedAxisGlobalOddFourthComparisonLocal 0)⁻¹, generatedAxisGlobalOddFourth_transporter 0⟩

/-- The actual negative original root-two transition has canonical Fourth destination. -/
theorem generatedAxisGlobalOddRoot02_negative_fourth_destination :
    ∃ h : H, sExtra.symm (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 2) generatedOddAxis) =
      rhoLocal h generatedFourthAxis :=
  ⟨(generatedAxisGlobalOddFourthComparisonLocal 1)⁻¹, generatedAxisGlobalOddFourth_transporter 1⟩

/-- The actual positive original root-four transition has canonical Fourth destination. -/
theorem generatedAxisGlobalOddRoot04_positive_fourth_destination :
    ∃ h : H, sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 4) generatedOddAxis) =
      rhoLocal h generatedFourthAxis :=
  ⟨(generatedAxisGlobalOddFourthComparisonLocal 2)⁻¹, generatedAxisGlobalOddFourth_transporter 2⟩

/-- The actual negative original root-four transition has canonical Fourth destination. -/
theorem generatedAxisGlobalOddRoot04_negative_fourth_destination :
    ∃ h : H, sExtra.symm (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 4) generatedOddAxis) =
      rhoLocal h generatedFourthAxis :=
  ⟨(generatedAxisGlobalOddFourthComparisonLocal 3)⁻¹, generatedAxisGlobalOddFourth_transporter 3⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
