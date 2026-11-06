/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthTensorColumn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthTensorHighPhysical

/-! Genuine coefficient squares separate the high rows and ensure a full nonzero spin column. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem original_short_squares (r : GriessShortIndex) :
    ((griessConwayEncode generatedOddAxis).2.1 r) ^ 2 = 0 ∨
    ((griessConwayEncode generatedOddAxis).2.1 r) ^ 2 = (1 / 16 : ℝ) ∨
    ((griessConwayEncode generatedOddAxis).2.1 r) ^ 2 = (9 / 16 : ℝ) := by
  rcases r with ⟨s, p⟩ | ⟨o, e⟩ | ⟨d, j⟩
  · rw [generatedSixth_original_pair_coordinate]
    split_ifs <;> norm_num
  · rw [show (griessConwayEncode generatedOddAxis).2.1
        (Sum.inr (Sum.inl (o, e))) = 0 from
        generatedAxis_triality_odd_octad_coordinate 0 0 0 o e]
    norm_num
  · rw [show (griessConwayEncode generatedOddAxis).2.1
        (Sum.inr (Sum.inr (d, j))) = 0 from
        generatedAxis_triality_odd_odd_coordinate 0 d 0 j 0]
    norm_num

/-- Every actual middle short coefficient has one of the three original discrete squares. -/
theorem generatedEighth_middle_short_squares (r : GriessShortIndex) :
    ((griessConwayEncode
      (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis)).2.1 r) ^ 2 = 0 ∨
    ((griessConwayEncode
      (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis)).2.1 r) ^ 2 =
        (1 / 16 : ℝ) ∨
    ((griessConwayEncode
      (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis)).2.1 r) ^ 2 =
        (9 / 16 : ℝ) := by
  rw [generatedFourth_local_short]
  change (qSign _ * (griessConwayEncode generatedOddAxis).2.1 _) ^ 2 = 0 ∨
    (qSign _ * (griessConwayEncode generatedOddAxis).2.1 _) ^ 2 = (1 / 16 : ℝ) ∨
    (qSign _ * (griessConwayEncode generatedOddAxis).2.1 _) ^ 2 = (9 / 16 : ℝ)
  simp only [mul_pow, pow_two (qSign _), qSign_sq, one_mul]
  exact original_short_squares _

/-- Every original odd contribution has square zero, sixty-four or five hundred seventy-six. -/
theorem generatedEighth_tensor_X_squares (t : SpinIndex) :
    (generatedEighthTensorXContribution t) ^ 2 = 0 ∨
    (generatedEighthTensorXContribution t) ^ 2 = 64 ∨
    (generatedEighthTensorXContribution t) ^ 2 = 576 := by
  rw [generatedEighth_tensor_X_square]
  rcases generatedEighth_middle_short_squares
    (Sum.inr (Sum.inr (spinDictionaryCode t, 20))) with h | h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/-- The whole actual outgoing twentieth tensor column is nonzero, without a spin-sign choice. -/
theorem generatedEighth_tensor_column_ne_zero (t : SpinIndex) :
    generatedEighthTensorColumn t ≠ 0 := by
  intro h
  rw [generatedEighth_tensor_column_coordinate] at h
  have he : (generatedEighthTensorXContribution t) ^ 2 =
      (generatedEighthTensorYContribution t 20) ^ 2 := by
    rw [eq_neg_of_add_eq_zero_left h, neg_sq]
  rw [generatedEighth_tensor_Y_twenty_square] at he
  rcases generatedEighth_tensor_X_squares t with hx | hx | hx <;> linarith

/-- All twelve actual high odd rows have the exact original high-quarter square. -/
theorem generatedEighth_high_odd_square (j : Fin 12) :
    ((griessConwayEncode
      (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis)).2.1
        (generatedEighthHighTarget j)) ^ 2 = (9 / 16 : ℝ) := by
  rw [generatedFourth_local_short, ← generatedEighth_high_permutation,
    localShortOperator_image, mul_pow, pow_two (qSign _), qSign_sq, one_mul]
  simp only [generatedEighthHighSource]
  rw [generatedSixth_original_pair_coordinate, generatedEighth_high_source_coordinates]
  simp only [true_or, ite_true]
  split_ifs <;> norm_num

/-- Each actual high odd code has original outgoing contribution of absolute value twenty-four. -/
theorem generatedEighth_tensor_X_high_square (j : Fin 12) (t : SpinIndex)
    (ht : spinDictionaryCode t = generatedEighthHighOddCode j) :
    (generatedEighthTensorXContribution t) ^ 2 = 576 := by
  rw [generatedEighth_tensor_X_square, ht]
  change 1024 * ((griessConwayEncode
    (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis)).2.1
      (generatedEighthHighTarget j)) ^ 2 = 576
  rw [generatedEighth_high_odd_square]
  norm_num

private theorem square_pair (x y : ℝ) (hx : x ^ 2 = 576) (hy : y ^ 2 = 4) :
    ((x + y) ^ 2 = 676 ∧ (-x + y) ^ 2 = 484) ∨
      ((x + y) ^ 2 = 484 ∧ (-x + y) ^ 2 = 676) := by
  have hx' : x = 24 ∨ x = -24 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (show x ^ 2 = (24 : ℝ) ^ 2 by norm_num; exact hx)
  have hy' : y = 2 ∨ y = -2 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (show y ^ 2 = (2 : ℝ) ^ 2 by norm_num; exact hy)
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;> norm_num

/-- Each high original omega pair has distinct denominator-cleared squares 676 and 484. -/
theorem generatedEighth_tensor_high_pair_squares (j : Fin 12) (t : SpinIndex)
    (ht : spinDictionaryCode t = generatedEighthHighOddCode j) :
    ((generatedEighthTensorColumn t) ^ 2 = 676 ∧
      (generatedEighthTensorColumn (t + Pi.single (11 : Fin 12) 1)) ^ 2 = 484) ∨
    ((generatedEighthTensorColumn t) ^ 2 = 484 ∧
      (generatedEighthTensorColumn (t + Pi.single (11 : Fin 12) 1)) ^ 2 = 676) := by
  rw [generatedEighth_tensor_column_coordinate, generatedEighth_tensor_column_coordinate,
    generatedEighth_tensor_X_omega, generatedEighth_tensor_Y_omega]
  exact square_pair _ _ (generatedEighth_tensor_X_high_square j t ht)
    (generatedEighth_tensor_Y_twenty_square t)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
