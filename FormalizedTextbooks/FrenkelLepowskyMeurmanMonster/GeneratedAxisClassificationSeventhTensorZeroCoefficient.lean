/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhTensorMaximum

/-! The genuine zero-spin tensor coordinate cannot vanish, fixing the remaining central phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original short-coordinate squares have exactly the three genuine quarter possibilities. -/
theorem generatedSeventh_original_short_square_values (r : GriessShortIndex) :
    ((griessConwayEncode generatedOddAxis).2.1 r) ^ 2 = 0 ∨
    ((griessConwayEncode generatedOddAxis).2.1 r) ^ 2 = (1 / 16 : ℝ) ∨
    ((griessConwayEncode generatedOddAxis).2.1 r) ^ 2 = (9 / 16 : ℝ) := by
  rcases r with ⟨s, p⟩ | ⟨o, e⟩ | ⟨d, j⟩
  · rw [generatedSeventh_original_pair_coordinate]
    split_ifs <;> norm_num
  · rw [show (griessConwayEncode generatedOddAxis).2.1
        (Sum.inr (Sum.inl (o, e))) = 0 from
        generatedAxis_triality_odd_octad_coordinate 0 0 0 o e]
    exact Or.inl (by norm_num)
  · rw [show (griessConwayEncode generatedOddAxis).2.1
        (Sum.inr (Sum.inr (d, j))) = 0 from
        generatedAxis_triality_odd_odd_coordinate 0 d 0 j 0]
    exact Or.inl (by norm_num)

/-- The actual local signed permutation retains all three original square possibilities. -/
theorem generatedSeventh_middle_short_square_values (r : GriessShortIndex) :
    ((griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).2.1 r) ^ 2 = 0 ∨
    ((griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).2.1 r) ^ 2 =
        (1 / 16 : ℝ) ∨
    ((griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).2.1 r) ^ 2 =
        (9 / 16 : ℝ) := by
  have h := generatedSeventh_original_short_square_values
    ((griessShortPermutation generatedSeventhLocalFiber.val.2).symm r)
  have he : ((griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).2.1 r) ^ 2 =
      ((griessConwayEncode generatedOddAxis).2.1
        ((griessShortPermutation generatedSeventhLocalFiber.val.2).symm r)) ^ 2 := by
    rw [generatedFourth_local_short]
    change (qSign _ * _) ^ 2 = _
    rw [mul_pow, pow_two (qSign _), qSign_sq, one_mul]
  simpa only [he] using h

/-- The zero-spin coordinate lies in the genuine support and has its exact square. -/
theorem generatedSeventh_spin_zero_square :
    (generatedSeventhSpinState (golayLabelCoefficients 0)) ^ 2 = (1 / 256 : ℝ) := by
  apply generatedSeventh_spin_kernel_square_exact
  have ht : (golayLabelCoefficients 0 : SpinIndex) = 0 := by ext i; fin_cases i <;> decide +kernel
  rw [ht, Matrix.mulVec_zero]

/-- The original Ω difference at code zero has the same exact nonzero square. -/
theorem generatedSeventh_spin_zero_difference_square :
    (generatedSeventhSpinState (golayLabelCoefficients 0) -
      generatedSeventhSpinState (golayLabelCoefficients 2048)) ^ 2 = (1 / 256 : ℝ) := by
  have h := generatedSeventh_spin_state_omega_product_zero (golayLabelCoefficients 0)
  have ho : golayLabelCoefficients 0 + Pi.single (11 : Fin 12) 1 =
      golayLabelCoefficients 2048 := golayLabel_low_add_omega (0 : Fin 2048)
  rw [ho] at h
  have hn : generatedSeventhSpinState (golayLabelCoefficients 0) ≠ 0 := by
    intro hn
    have he := generatedSeventh_spin_zero_square
    rw [hn] at he
    norm_num at he
  have hz := (mul_eq_zero.mp h).resolve_left hn
  rw [hz, sub_zero]
  exact generatedSeventh_spin_zero_square

/-- The original outgoing Y contribution has exact square one at zero spin. -/
theorem generatedSeventh_tensor_Y_zero_square :
    (generatedSeventhTensorYContribution (golayLabelCoefficients 0) 16) ^ 2 = 1 := by
  rw [generatedSeventh_tensor_Y_state]
  have hd : spinDictionaryCode (golayLabelCoefficients 0) = 0 :=
    spinDictionaryCode_low (0 : Fin 2048)
  have hc : generatedSeventhFrameVectorData 7 0 16 = 1 := by decide +kernel
  simp only [hd, hc, Fin.val_zero, Int.cast_one]
  change (-16 * (1 : ℝ) * _ * _ *
    (generatedSeventhSpinState (golayLabelCoefficients 0) -
      generatedSeventhSpinState (golayLabelCoefficients 2048))) ^ 2 = 1
  rw [mul_pow, mul_pow, mul_pow, mul_pow, generatedSeventh_spin_zero_difference_square,
    pow_two (qSign _), qSign_sq]
  split_ifs <;> norm_num

/-- The incoming odd contribution at zero spin has square zero or sixty-four. -/
theorem generatedSeventh_tensor_X_zero_square :
    (generatedSeventhTensorXContribution (golayLabelCoefficients 0)) ^ 2 = 0 ∨
      (generatedSeventhTensorXContribution (golayLabelCoefficients 0)) ^ 2 = 64 := by
  rw [generatedSeventh_tensor_X_square]
  have hd : spinDictionaryCode (golayLabelCoefficients 0) = 0 :=
    spinDictionaryCode_low (0 : Fin 2048)
  rw [hd]
  have h := generatedSeventh_middle_short_square_values (Sum.inr (Sum.inr (0, 16)))
  rcases h with h | h | h
  · rw [h]
    exact Or.inl (by norm_num)
  · rw [h]
    exact Or.inr (by norm_num)
  · have hb := generatedSeventh_middle_odd_sixteen_small 0 (by decide)
    nlinarith only [h, hb]

/-- The genuine zero-spin tensor coefficient is nonzero without needing its absolute sign. -/
theorem generatedSeventh_tensor_zero_nonzero : generatedSeventhTensorColumn 0 ≠ 0 := by
  have ht : (golayLabelCoefficients 0 : SpinIndex) = 0 := by ext i; fin_cases i <;> decide +kernel
  have hx := generatedSeventh_tensor_X_zero_square
  have hy := generatedSeventh_tensor_Y_zero_square
  rw [ht] at hx hy
  intro hz
  rw [generatedSeventh_tensor_column_coordinate] at hz
  have he : generatedSeventhTensorXContribution 0 = -generatedSeventhTensorYContribution 0 16 := by
    linarith only [hz]
  rcases hx with hx | hx <;> rw [he, neg_sq] at hx <;> nlinarith only [hx, hy]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
