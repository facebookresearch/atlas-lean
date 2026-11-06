/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorCircuitActions

/-! Equivalent complete monomial address certificates with the post label shared inside its
quadratic phase. Every original coordinate and central sign is retained. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact finite source-address conditions for both compact monomial boundaries. -/
def generatedNinthLowerSpinTensorCachedAddressCondition (i : Fin 11) (n : Fin 4096) : Prop :=
  let t := golayLabelCoefficients n
  generatedNinthLowerSpinTensorPreLabel i n =
      nortonUIntegerLabel ((generatedNinthLowerSpinCompactRight i).symm t) ∧
    generatedNinthLowerSpinTensorPreSign i n =
      nortonUIntegerSign (monsterMonomialQuadratic
        (generatedNinthLowerSpinCompactPhase (generatedNinthLowerSpinCompactSecondPhaseRows i))
          t) ∧
    generatedNinthLowerSpinTensorPostLabel i n = nortonUIntegerLabel
      ((generatedNinthLowerSpinCompactLeft i).symm
        (t + spinTranslation (generatedNinthLowerSpinCompactPauli i))) ∧
    generatedNinthLowerSpinTensorPostSign i n =
      nortonUIntegerSign (spinPhase (generatedNinthLowerSpinCompactPauli i) t) *
        nortonUIntegerSign (monsterMonomialQuadratic
          (generatedNinthLowerSpinCompactPhase (generatedNinthLowerSpinCompactFirstPhaseRows i))
            (golayLabelCoefficients (generatedNinthLowerSpinTensorPostLabel i n)))

/-- The verified post address evaluates the same quadratic phase as the full inverse action. -/
theorem generatedNinth_lower_spin_tensor_address_of_cached (i : Fin 11) (n : Fin 4096)
    (h : generatedNinthLowerSpinTensorCachedAddressCondition i n) :
    generatedNinthLowerSpinTensorAddressCondition i n := by
  unfold generatedNinthLowerSpinTensorCachedAddressCondition at h
  unfold generatedNinthLowerSpinTensorAddressCondition
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  have hp := congrArg golayLabelCoefficients h.2.2.1
  simp only [nortonUIntegerLabel_inverse] at hp
  simpa only [hp] using h.2.2.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
