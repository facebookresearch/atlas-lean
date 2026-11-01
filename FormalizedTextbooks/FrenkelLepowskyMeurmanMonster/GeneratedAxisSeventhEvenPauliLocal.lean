/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSignAxisLift

/-! Even-modulation Pauli conjugates are local with their original Golay sign projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every even-modulation Pauli has a local triality conjugate and exact sign projection. -/
theorem generatedSeventh_even_pauli_local (q : Q) (hq : spinModulation q 11 = 0) :
    ∃ d : Fin 4096, golayLabelCoefficients d = spinTranslation q ∧ ∃ h : H,
      localIntoGenerated h = extraIntoGenerated * qIntoGenerated q * extraIntoGenerated⁻¹ ∧
      projH h = (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode d)) : Co1) := by
  let d := sourceCodeLabelEquiv.symm (spinTranslation q)
  have hd : golayLabelCoefficients d = spinTranslation q := sourceCodeLabelEquiv.apply_symm_apply _
  have ht : spinTranslation q = golayLabelCoefficients d +
      (0 : ZMod 2) • Pi.single (11 : Fin 12) 1 := by rw [zero_smul, add_zero, hd]
  obtain ⟨m, hm, ε, he⟩ := generatedSeventh_sign_pauli_factor q d 0 ht hq
  refine ⟨d, hd, generatedSeventhCorrectedSignLocal m 0 d ε, ?_,
    generatedSeventh_corrected_sign_projection _ _ _ _⟩
  rw [generatedSeventh_corrected_sign_generated m hm, ← he]

/-- Pauli elements preserve the entire physical matrix, without any spin-fixation assumption. -/
theorem generatedSeventh_Q_matrix (q : Q) (x : GriessSpace) :
    (griessConwayEncode (rhoLocal (inclQ q) x)).1 = (griessConwayEncode x).1 := by
  change (griessConwayEncode (rhoLocal (localFiberIntoH (localFiberIncl q)) x)).1 = _
  rw [generatedFourth_local_matrix]
  change conwayMatrixAction 1 _ = _
  rw [map_one]
  rfl

/-- The entire matrix action of the corrected local sign is its genuine physical Golay sign. -/
theorem generatedSeventh_corrected_sign_matrix (m : SpinIndex) (β : ZMod 2)
    (d : Fin 4096) (ε : ZMod 2) (x : GriessSpace) :
    (griessConwayEncode (rhoLocal (generatedSeventhCorrectedSignLocal m β d ε) x)).1 =
      conwayMatrixAction (golaySignIsometry (sourceGeneratedSignCode d))
        (griessConwayEncode x).1 := by
  simp only [generatedSeventhCorrectedSignLocal, map_mul, LinearEquiv.mul_apply]
  rw [generatedSeventh_Q_matrix, generatedSeventh_Q_matrix]
  have h := congrArg Subtype.val (generatedSeventh_source_sign_local_generated d ε)
  change rhoLocal (generatedSeventhSourceSignLocal d ε) =
    (generatedSeventhSourceZ d ε).val at h
  rw [h]
  exact generatedSeventh_source_sign_matrix d ε x

/-- Even Pauli conjugates admit a local lift with the original sign matrix action. -/
theorem generatedSeventh_even_pauli_local_matrix (q : Q) (hq : spinModulation q 11 = 0) :
    ∃ d : Fin 4096, golayLabelCoefficients d = spinTranslation q ∧ ∃ h : H,
      localIntoGenerated h = extraIntoGenerated * qIntoGenerated q * extraIntoGenerated⁻¹ ∧
      projH h = (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode d)) : Co1) ∧
      ∀ x : GriessSpace, (griessConwayEncode (rhoLocal h x)).1 =
        conwayMatrixAction (golaySignIsometry (sourceGeneratedSignCode d))
          (griessConwayEncode x).1 := by
  let d := sourceCodeLabelEquiv.symm (spinTranslation q)
  have hd : golayLabelCoefficients d = spinTranslation q := sourceCodeLabelEquiv.apply_symm_apply _
  have ht : spinTranslation q = golayLabelCoefficients d +
      (0 : ZMod 2) • Pi.single (11 : Fin 12) 1 := by rw [zero_smul, add_zero, hd]
  obtain ⟨m, hm, ε, he⟩ := generatedSeventh_sign_pauli_factor q d 0 ht hq
  refine ⟨d, hd, generatedSeventhCorrectedSignLocal m 0 d ε, ?_,
    generatedSeventh_corrected_sign_projection _ _ _ _, ?_⟩
  · rw [generatedSeventh_corrected_sign_generated m hm, ← he]
  · exact generatedSeventh_corrected_sign_matrix m 0 d ε

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
