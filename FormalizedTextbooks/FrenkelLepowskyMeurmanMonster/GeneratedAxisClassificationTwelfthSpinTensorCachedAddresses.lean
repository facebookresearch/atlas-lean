/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorCircuitActions

/-! Equivalent complete monomial address certificates with the post label shared inside its
quadratic phase. Every original coordinate and central sign is retained. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact finite source-address conditions for both compact monomial boundaries. -/
def generatedTwelfthSpinTensorCachedAddressCondition (i : Fin 12) (n : Fin 4096) : Prop :=
  let t := golayLabelCoefficients n
  generatedTwelfthSpinTensorPreLabel i n =
      nortonUIntegerLabel ((generatedTwelfthSpinCompactRight i).symm t) ∧
    generatedTwelfthSpinTensorPreSign i n =
      nortonUIntegerSign (monsterMonomialQuadratic
        (generatedTwelfthSpinCompactPhase (generatedTwelfthSpinCompactSecondPhaseRows i))
          t) ∧
    generatedTwelfthSpinTensorPostLabel i n = nortonUIntegerLabel
      ((generatedTwelfthSpinCompactLeft i).symm
        (t + spinTranslation (generatedTwelfthSpinCompactPauli i))) ∧
    generatedTwelfthSpinTensorPostSign i n =
      nortonUIntegerSign (spinPhase (generatedTwelfthSpinCompactPauli i) t) *
        nortonUIntegerSign (monsterMonomialQuadratic
          (generatedTwelfthSpinCompactPhase (generatedTwelfthSpinCompactFirstPhaseRows i))
            (golayLabelCoefficients (generatedTwelfthSpinTensorPostLabel i n)))

/-- The verified post address evaluates the same quadratic phase as the full inverse action. -/
theorem generatedTwelfth_spin_tensor_address_of_cached (i : Fin 12) (n : Fin 4096)
    (h : generatedTwelfthSpinTensorCachedAddressCondition i n) :
    generatedTwelfthSpinTensorAddressCondition i n := by
  unfold generatedTwelfthSpinTensorCachedAddressCondition at h
  unfold generatedTwelfthSpinTensorAddressCondition
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  have hp := congrArg golayLabelCoefficients h.2.2.1
  simp only [nortonUIntegerLabel_inverse] at hp
  simpa only [hp] using h.2.2.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
