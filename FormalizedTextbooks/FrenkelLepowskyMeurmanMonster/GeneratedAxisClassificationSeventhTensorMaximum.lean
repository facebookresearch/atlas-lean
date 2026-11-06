/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhTensorCoordinates

/-! One actual tensor coordinate has a unique absolute maximum, with no spin-cache assumption. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem square_pair (x y : ℝ) (hx : x ^ 2 = 576) (hy : y ^ 2 = 1) :
    ((x + y) ^ 2 = 625 ∧ (-x + y) ^ 2 = 529) ∨
      ((x + y) ^ 2 = 529 ∧ (-x + y) ^ 2 = 625) := by
  have hx' : x = 24 ∨ x = -24 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (show x ^ 2 = (24 : ℝ) ^ 2 by norm_num; exact hx)
  have hy' : y = 1 ∨ y = -1 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (show y ^ 2 = (1 : ℝ) ^ 2 by simpa only [one_pow] using hy)
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;> norm_num

/-- The two genuine exceptional Ω coordinates have squares 625 and 529 in some order. -/
theorem generatedSeventh_tensor_exceptional_squares :
    ((generatedSeventhTensorColumn (golayLabelCoefficients 1012)) ^ 2 = 625 ∧
      (generatedSeventhTensorColumn (golayLabelCoefficients 3060)) ^ 2 = 529) ∨
    ((generatedSeventhTensorColumn (golayLabelCoefficients 1012)) ^ 2 = 529 ∧
      (generatedSeventhTensorColumn (golayLabelCoefficients 3060)) ^ 2 = 625) := by
  have ho : golayLabelCoefficients 1012 + Pi.single (11 : Fin 12) 1 =
      golayLabelCoefficients 3060 := golayLabel_low_add_omega (1012 : Fin 2048)
  rw [← ho, generatedSeventh_tensor_column_coordinate,
    generatedSeventh_tensor_column_coordinate, generatedSeventh_tensor_X_omega,
    generatedSeventh_tensor_Y_omega]
  exact square_pair _ _ generatedSeventh_tensor_X_high_square generatedSeventh_tensor_Y_high_square

/-- Every other original tensor code has denominator-cleared absolute value at most nine. -/
theorem generatedSeventh_tensor_column_small (t : SpinIndex) (ht : spinDictionaryCode t ≠ 1012) :
    (generatedSeventhTensorColumn t) ^ 2 ≤ 81 := by
  rw [generatedSeventh_tensor_column_coordinate]
  have hx := generatedSeventh_tensor_X_small t ht
  have hy := generatedSeventh_tensor_Y_sixteen_bound t
  have hxl : -8 ≤ generatedSeventhTensorXContribution t := by nlinarith only [hx]
  have hxu : generatedSeventhTensorXContribution t ≤ 8 := by nlinarith only [hx]
  have hyl : -1 ≤ generatedSeventhTensorYContribution t 16 := by nlinarith only [hy]
  have hyu : generatedSeventhTensorYContribution t 16 ≤ 1 := by nlinarith only [hy]
  nlinarith only [hxl, hxu, hyl, hyu]

private theorem code_exceptional (t : SpinIndex) (ht : spinDictionaryCode t = 1012) :
    t = golayLabelCoefficients 1012 ∨ t = golayLabelCoefficients 3060 := by
  have h := spinDictionaryIndex_cases t
  have hl : (⟨(1012 : Fin 2048).val, by omega⟩ : Fin 4096) = 1012 := by
    apply Fin.ext
    norm_num
  have hh : (⟨(1012 : Fin 2048).val + 2048, by omega⟩ : Fin 4096) = 3060 := by
    apply Fin.ext
    norm_num
  simpa only [ht, hl, hh] using h

/-- The actual original tensor column has one and only one coordinate with square 625. -/
theorem generatedSeventh_tensor_unique_maximum :
    ∃ t : SpinIndex, (generatedSeventhTensorColumn t) ^ 2 = 625 ∧
      ∀ u : SpinIndex, (generatedSeventhTensorColumn u) ^ 2 = 625 → u = t := by
  rcases generatedSeventh_tensor_exceptional_squares with h | h
  · refine ⟨golayLabelCoefficients 1012, h.1, ?_⟩
    intro u hu
    by_cases hc : spinDictionaryCode u = 1012
    · rcases code_exceptional u hc with rfl | rfl
      · rfl
      · nlinarith only [h.2, hu]
    · have hb := generatedSeventh_tensor_column_small u hc
      nlinarith only [hb, hu]
  · refine ⟨golayLabelCoefficients 3060, h.2, ?_⟩
    intro u hu
    by_cases hc : spinDictionaryCode u = 1012
    · rcases code_exceptional u hc with rfl | rfl
      · nlinarith only [h.1, hu]
      · rfl
    · have hb := generatedSeventh_tensor_column_small u hc
      nlinarith only [hb, hu]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
