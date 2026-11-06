/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineParameterBasis

/-! The literal translation, modulation and central phases of the seven actual affine generators. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual binary translation labels of the seven free-coordinate Q generators. -/
def generatedFourthQAffineParameterBasisTranslationLabels : Fin 7 → Fin 4096 :=
  ![2048, 14, 14, 14, 0, 0, 0]

/-- The actual binary modulation labels of the same seven Q generators. -/
def generatedFourthQAffineParameterBasisModulationLabels : Fin 7 → Fin 4096 :=
  ![0, 1, 16, 32, 64, 128, 1024]

/-- The actual central sign bits, including the nontrivial translation corrections. -/
def generatedFourthQAffineParameterBasisCentralPhases : Fin 7 → ZMod 2 :=
  ![1, 1, 1, 1, 0, 0, 1]

private theorem fourth_basis_translation : ∀ i : Fin 7, ∀ j : Fin 12,
    spinTranslation (generatedFourthQAffineParameterBasis i) j =
      golayLabelCoefficients (generatedFourthQAffineParameterBasisTranslationLabels i) j := by
  decide +kernel

private theorem fourth_basis_modulation : ∀ i : Fin 7, ∀ j : Fin 12,
    spinModulation (generatedFourthQAffineParameterBasis i) j =
      golayLabelCoefficients (generatedFourthQAffineParameterBasisModulationLabels i) j := by
  decide +kernel

private theorem fourth_basis_central : ∀ i : Fin 7,
    Multiplicative.toAdd (generatedFourthQAffineParameterBasis i).coeff =
      generatedFourthQAffineParameterBasisCentralPhases i := by
  decide +kernel

/-- Every counted coordinate generator is exactly the displayed original Q element. -/
theorem generatedFourthQAffineParameterBasis_literal : ∀ i : Fin 7,
    generatedFourthQAffineParameterBasis i = generatedAxisFourthQFromSpin
      (golayLabelCoefficients (generatedFourthQAffineParameterBasisTranslationLabels i))
      (golayLabelCoefficients (generatedFourthQAffineParameterBasisModulationLabels i))
      (generatedFourthQAffineParameterBasisCentralPhases i) := by
  intro i
  apply generatedAxisFourthQ_spin_coordinates_injective
  · rw [generatedAxisFourthQFromSpin_translation]
    exact funext (fourth_basis_translation i)
  · rw [generatedAxisFourthQFromSpin_modulation]
    exact funext (fourth_basis_modulation i)
  · rw [generatedAxisFourthQFromSpin_coeff]
    exact fourth_basis_central i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
