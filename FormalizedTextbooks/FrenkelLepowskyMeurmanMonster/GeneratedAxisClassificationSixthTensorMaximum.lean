/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorCoordinates

/-! One actual tensor coordinate has a unique absolute maximum, with no spin-cache assumption. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem square_pair (x y : ℝ) (hx : x ^ 2 = 576) (hy : y ^ 2 = 9) :
    ((x + y) ^ 2 = 729 ∧ (-x + y) ^ 2 = 441) ∨
      ((x + y) ^ 2 = 441 ∧ (-x + y) ^ 2 = 729) := by
  have hx' : x = 24 ∨ x = -24 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (show x ^ 2 = (24 : ℝ) ^ 2 by norm_num; exact hx)
  have hy' : y = 3 ∨ y = -3 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (show y ^ 2 = (3 : ℝ) ^ 2 by norm_num; exact hy)
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;> norm_num

/-- The two genuine exceptional Ω coordinates have squares 729 and 441 in some order. -/
theorem generatedSixth_tensor_exceptional_squares :
    ((generatedSixthTensorColumn (golayLabelCoefficients 1010)) ^ 2 = 729 ∧
      (generatedSixthTensorColumn (golayLabelCoefficients 3058)) ^ 2 = 441) ∨
    ((generatedSixthTensorColumn (golayLabelCoefficients 1010)) ^ 2 = 441 ∧
      (generatedSixthTensorColumn (golayLabelCoefficients 3058)) ^ 2 = 729) := by
  have ho : golayLabelCoefficients 1010 + Pi.single (11 : Fin 12) 1 =
      golayLabelCoefficients 3058 := golayLabel_low_add_omega (1010 : Fin 2048)
  rw [← ho, generatedSixth_tensor_column_coordinate,
    generatedSixth_tensor_column_coordinate, generatedSixth_tensor_X_omega,
    generatedSixth_tensor_Y_omega]
  exact square_pair _ _ generatedSixth_tensor_X_high_square generatedSixth_tensor_Y_high_square

/-- Every other original tensor code has denominator-cleared absolute value at most eleven. -/
theorem generatedSixth_tensor_column_small (t : SpinIndex) (ht : spinDictionaryCode t ≠ 1010) :
    (generatedSixthTensorColumn t) ^ 2 ≤ 121 := by
  rw [generatedSixth_tensor_column_coordinate]
  have hx := generatedSixth_tensor_X_small t ht
  have hy := generatedSixth_tensor_Y_sixteen_bound t
  have hxl : -8 ≤ generatedSixthTensorXContribution t := by nlinarith only [hx]
  have hxu : generatedSixthTensorXContribution t ≤ 8 := by nlinarith only [hx]
  have hyl : -3 ≤ generatedSixthTensorYContribution t 16 := by nlinarith only [hy]
  have hyu : generatedSixthTensorYContribution t 16 ≤ 3 := by nlinarith only [hy]
  nlinarith only [hxl, hxu, hyl, hyu]

private theorem code_exceptional (t : SpinIndex) (ht : spinDictionaryCode t = 1010) :
    t = golayLabelCoefficients 1010 ∨ t = golayLabelCoefficients 3058 := by
  have h := spinDictionaryIndex_cases t
  have hl : (⟨(1010 : Fin 2048).val, by omega⟩ : Fin 4096) = 1010 := by
    apply Fin.ext
    norm_num
  have hh : (⟨(1010 : Fin 2048).val + 2048, by omega⟩ : Fin 4096) = 3058 := by
    apply Fin.ext
    norm_num
  simpa only [ht, hl, hh] using h

/-- The actual original tensor column has one and only one coordinate with square 729. -/
theorem generatedSixth_tensor_unique_maximum :
    ∃ t : SpinIndex, (generatedSixthTensorColumn t) ^ 2 = 729 ∧
      ∀ u : SpinIndex, (generatedSixthTensorColumn u) ^ 2 = 729 → u = t := by
  rcases generatedSixth_tensor_exceptional_squares with h | h
  · refine ⟨golayLabelCoefficients 1010, h.1, ?_⟩
    intro u hu
    by_cases hc : spinDictionaryCode u = 1010
    · rcases code_exceptional u hc with rfl | rfl
      · rfl
      · nlinarith only [h.2, hu]
    · have hb := generatedSixth_tensor_column_small u hc
      nlinarith only [hb, hu]
  · refine ⟨golayLabelCoefficients 3058, h.2, ?_⟩
    intro u hu
    by_cases hc : spinDictionaryCode u = 1010
    · rcases code_exceptional u hc with rfl | rfl
      · nlinarith only [h.1, hu]
      · rfl
    · have hb := generatedSixth_tensor_column_small u hc
      nlinarith only [hb, hu]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
