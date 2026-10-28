/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpinSupportData

/-! Genuine fixing Pauli elements over every translation satisfying the three support equations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every admissible translation is reconstructed by the original nine fixing Pauli columns. -/
theorem generatedSeventh_spin_translation_reconstruct (u : SpinIndex)
    (hu : generatedSeventhSpinSupportMatrix *ᵥ u = 0) :
    generatedSeventhSpinPauliTranslationMatrix *ᵥ
      (generatedSeventhSpinPauliLeftInverse *ᵥ u) = u := by
  have h := congrArg (fun M => M *ᵥ u)
    generatedSeventh_spin_support_projection_certificate
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu,
    Matrix.mulVec_zero, add_zero, Matrix.one_mulVec] at h
  exact h

/-- Each translation satisfying the support equations has an actual full-phase fixing lift. -/
theorem generatedSeventh_spin_translation_lift (u : SpinIndex)
    (hu : generatedSeventhSpinSupportMatrix *ᵥ u = 0) :
    ∃ q : Q, spinTranslation q = u ∧
      spinRepresentation q generatedSeventhSpinState = generatedSeventhSpinState := by
  refine ⟨generatedSeventhSpinPauliProduct (generatedSeventhSpinPauliLeftInverse *ᵥ u),
    ?_, generatedSeventh_spin_pauli_product_fixed _⟩
  rw [generatedSeventh_spin_pauli_product_translation]
  exact generatedSeventh_spin_translation_reconstruct u hu

/-- The actual fixing odd modulation changes no translation and toggles modulation coordinate 11. -/
theorem generatedSeventh_spin_odd_modulation_coordinates :
    spinTranslation (cocodeQ (golayLabelCoefficients 3079)) = 0 ∧
      spinModulation (cocodeQ (golayLabelCoefficients 3079)) 11 = 1 := by
  constructor
  · exact cocodeQ_translation _
  · decide +kernel

/-- A fixing lift of each admissible translation can retain even modulation coordinate 11. -/
theorem generatedSeventh_spin_translation_even_lift (u : SpinIndex)
    (hu : generatedSeventhSpinSupportMatrix *ᵥ u = 0) :
    ∃ q : Q, spinTranslation q = u ∧ spinModulation q 11 = 0 ∧
      spinRepresentation q generatedSeventhSpinState = generatedSeventhSpinState := by
  obtain ⟨q, hq, hf⟩ := generatedSeventh_spin_translation_lift u hu
  by_cases hm : spinModulation q 11 = 0
  · exact ⟨q, hq, hm, hf⟩
  · have hm1 : spinModulation q 11 = 1 := by
      have hh : ∀ b : ZMod 2, b ≠ 0 → b = 1 := by decide
      exact hh _ hm
    let d := cocodeQ (golayLabelCoefficients 3079)
    have hd := generatedSeventh_spin_support_modulation_fixed (1 : Fin 3)
    change spinRepresentation d generatedSeventhSpinState = generatedSeventhSpinState at hd
    refine ⟨d * q, ?_, ?_, ?_⟩
    · rw [spinTranslation_mul, generatedSeventh_spin_odd_modulation_coordinates.1,
        zero_add, hq]
    · rw [spinModulation_mul]
      change spinModulation d 11 + spinModulation q 11 = 0
      rw [generatedSeventh_spin_odd_modulation_coordinates.2, hm1]
      decide
    · change d * q ∈ generatedSeventhSpinStateStabilizer
      exact generatedSeventhSpinStateStabilizer.mul_mem hd hf

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
