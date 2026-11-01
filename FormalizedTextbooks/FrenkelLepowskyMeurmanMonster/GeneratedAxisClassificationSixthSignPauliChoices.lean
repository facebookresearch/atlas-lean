/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddlePauliFull
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSignSpatial

/-! Actual even-modulation middle fixers realizing every selected sign modulo Ω. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The selected sign translation adjusted by Ω to satisfy the third support equation. -/
def generatedSixthSignPauliTranslation (j : Fin 10) : SpinIndex :=
  golayLabelCoefficients (generatedSixthMonomialSignCode j) +
    spinDot (golayLabelCoefficients 3079)
      (golayLabelCoefficients (generatedSixthMonomialSignCode j)) • Pi.single 11 1

/-- A genuine full middle-axis fixer having the selected adjusted translation. -/
def generatedSixthSignPauliBase (j : Fin 10) : Q :=
  generatedSixthSpinPauliProduct
    (generatedSixthSpinPauliLeftInverse *ᵥ generatedSixthSignPauliTranslation j)

/-- Multiplication by a genuine fixing pure modulation makes the modulation even. -/
def generatedSixthSignPauliChoice (j : Fin 10) : Q :=
  generatedSixthSignPauliBase j *
    (cocodeQ (golayLabelCoefficients 3079)) ^
      (spinModulation (generatedSixthSignPauliBase j) 11).val

/-- The ten adjusted source translations satisfy all three original support equations. -/
theorem generatedSixth_sign_pauli_support_certificate (j : Fin 10) :
    generatedSixthSpinSupportMatrix *ᵥ generatedSixthSignPauliTranslation j = 0 := by
  fin_cases j <;> decide +kernel

/-- Each genuine choice has exactly the intended original binary translation. -/
theorem generatedSixth_sign_pauli_translation (j : Fin 10) :
    spinTranslation (generatedSixthSignPauliChoice j) =
      generatedSixthSignPauliTranslation j := by
  have hp := congrArg (fun M : Matrix (Fin 12) (Fin 12) (ZMod 2) =>
    M *ᵥ generatedSixthSignPauliTranslation j)
    generatedSixth_spin_support_projection_certificate
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    generatedSixth_sign_pauli_support_certificate, Matrix.mulVec_zero, add_zero,
    Matrix.one_mulVec] at hp
  unfold generatedSixthSignPauliChoice generatedSixthSignPauliBase
  rw [spinTranslation_mul, generatedSixth_spin_pauli_product_translation]
  have hz : spinTranslation ((cocodeQ (golayLabelCoefficients 3079)) ^
      (spinModulation (generatedSixthSignPauliBase j) 11).val) = 0 := by
    generalize spinModulation (generatedSixthSignPauliBase j) 11 = b
    have hb : b = 0 ∨ b = 1 := by revert b; decide +kernel
    rcases hb with rfl | rfl <;> simp only [ZMod.val_zero, ZMod.val_one,
      pow_zero, pow_one, cocodeQ_translation]; rfl
  dsimp only [generatedSixthSignPauliBase] at hz
  rw [hz, add_zero]
  exact hp

/-- Every selected Pauli choice has modulation zero on Ω. -/
theorem generatedSixth_sign_pauli_even (j : Fin 10) :
    spinModulation (generatedSixthSignPauliChoice j) 11 = 0 := by
  unfold generatedSixthSignPauliChoice
  rw [spinModulation_mul]
  change spinModulation (generatedSixthSignPauliBase j) 11 + _ = 0
  generalize spinModulation (generatedSixthSignPauliBase j) 11 = b
  have hb : b = 0 ∨ b = 1 := by revert b; decide +kernel
  rcases hb with rfl | rfl
  · rfl
  · change (1 : ZMod 2) + golayLabelCoefficients 3079 11 = 0
    decide +kernel

/-- The actual choices fix the entire genuine middle vector, including short coordinates. -/
theorem generatedSixth_sign_pauli_full_fixed (j : Fin 10) :
    rhoLocal (inclQ (generatedSixthSignPauliChoice j)) generatedSixthMiddleAxis =
      generatedSixthMiddleAxis := by
  change generatedSixthSignPauliChoice j ∈ generatedSixthMiddleAxisQStabilizer
  apply generatedSixthMiddleAxisQStabilizer.mul_mem
  · exact generatedSixth_pauli_product_full_fixed _
  · apply generatedSixthMiddleAxisQStabilizer.pow_mem
    exact generatedSixth_support_modulation_full_fixed 1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
