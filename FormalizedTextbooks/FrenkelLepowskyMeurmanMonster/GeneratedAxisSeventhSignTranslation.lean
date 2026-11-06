/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSpinTranslationLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSignParameterBinding

/-! A central Omega correction places every admissible sign in the fixing translation space. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual parity selecting the required central Omega correction. -/
def generatedSeventhSignOmegaCorrection (a : SpinIndex) : ZMod 2 :=
  spinDot (golayLabelCoefficients 3079) a

/-- The first and third spin support equations are the actual triangle-sign equations. -/
theorem generatedSeventh_sign_support_rows :
    generatedSeventhSpinSupportMatrix 0 = generatedSeventhSignParameterMatrix 0 ∧
      generatedSeventhSpinSupportMatrix 2 =
        generatedSeventhSignParameterMatrix 0 + generatedSeventhSignParameterMatrix 1 := by
  decide +kernel

/-- Omega has zero first and third support syndrome and toggles the second equation. -/
theorem generatedSeventh_sign_omega_support :
    generatedSeventhSpinSupportMatrix *ᵥ (Pi.single (11 : Fin 12) 1) =
      Pi.single (1 : Fin 3) 1 := by
  decide +kernel

/-- The chosen central correction makes every original matrix-preserving sign translation valid. -/
theorem generatedSeventh_sign_corrected_translation (a : SpinIndex)
    (ha : a ∈ generatedSeventhSignParameterSpace) :
    generatedSeventhSpinSupportMatrix *ᵥ
      (a + generatedSeventhSignOmegaCorrection a • Pi.single (11 : Fin 12) 1) = 0 := by
  have ha0 : generatedSeventhSignParameterMatrix *ᵥ a = 0 := ha
  have h0 : generatedSeventhSignParameterMatrix 0 ⬝ᵥ a = 0 := congrFun ha0 0
  have h1 : generatedSeventhSignParameterMatrix 1 ⬝ᵥ a = 0 := congrFun ha0 1
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, generatedSeventh_sign_omega_support]
  ext j
  fin_cases j
  · change generatedSeventhSpinSupportMatrix 0 ⬝ᵥ a + _ = 0
    rw [generatedSeventh_sign_support_rows.1]
    change generatedSeventhSignParameterMatrix 0 ⬝ᵥ a +
      generatedSeventhSignOmegaCorrection a * 0 = 0
    rw [mul_zero, add_zero, h0]
  · change spinDot (golayLabelCoefficients 3079) a +
      generatedSeventhSignOmegaCorrection a * 1 = 0
    simp only [generatedSeventhSignOmegaCorrection, mul_one, CharTwo.add_self_eq_zero]
  · change generatedSeventhSpinSupportMatrix 2 ⬝ᵥ a + _ = 0
    rw [generatedSeventh_sign_support_rows.2, add_dotProduct]
    change generatedSeventhSignParameterMatrix 0 ⬝ᵥ a +
      generatedSeventhSignParameterMatrix 1 ⬝ᵥ a +
      generatedSeventhSignOmegaCorrection a * 0 = 0
    rw [h0, h1, mul_zero, zero_add, zero_add]

/-- Every admissible actual sign admits a full-phase fixing lift with the corrected translation. -/
theorem generatedSeventh_sign_fixing_pauli (a : SpinIndex)
    (ha : a ∈ generatedSeventhSignParameterSpace) :
    ∃ q : Q,
      spinTranslation q =
        a + generatedSeventhSignOmegaCorrection a • Pi.single (11 : Fin 12) 1 ∧
      spinModulation q 11 = 0 ∧
      spinRepresentation q generatedSeventhSpinState = generatedSeventhSpinState :=
  generatedSeventh_spin_translation_even_lift _
    (generatedSeventh_sign_corrected_translation a ha)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
