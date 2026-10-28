/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQSupportData

/-! Every selected original quotient witness has a genuine nonzero full-axis short coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual full-axis coefficient of each selected original physical short witness. -/
theorem generatedTenth_Q_support_coordinate (j : Fin 23) :
    (griessConwayEncode generatedTenthAxis).2.1 (generatedTenthQSupportIndex j) =
      (generatedTenthQSupportNumerator j : ℝ) / 128 := by
  fin_cases j
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inl (0, 2)) = (4 : ℝ) / 128
    rw [generatedTenth_final_pair_q, generatedTenthQSupportCoefficient00]
    push_cast
    rfl
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inl (1, 2)) = (12 : ℝ) / 128
    rw [generatedTenth_final_pair_q, generatedTenthQSupportCoefficient01]
    push_cast
    rfl
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inl (0, 3)) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedTenth_final_pair_q, generatedTenthQSupportCoefficient02]
    push_cast
    rfl
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inl (0, 4)) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedTenth_final_pair_q, generatedTenthQSupportCoefficient03]
    push_cast
    rfl
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inl (0, 5)) = (4 : ℝ) / 128
    rw [generatedTenth_final_pair_q, generatedTenthQSupportCoefficient04]
    push_cast
    rfl
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inl (0, 6)) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedTenth_final_pair_q, generatedTenthQSupportCoefficient05]
    push_cast
    rfl
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inl (0, 8)) = (4 : ℝ) / 128
    rw [generatedTenth_final_pair_q, generatedTenthQSupportCoefficient06]
    push_cast
    rfl
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inl (0, 9)) = (4 : ℝ) / 128
    rw [generatedTenth_final_pair_q, generatedTenthQSupportCoefficient07]
    push_cast
    rfl
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inl (0, 11)) = (4 : ℝ) / 128
    rw [generatedTenth_final_pair_q, generatedTenthQSupportCoefficient08]
    push_cast
    rfl
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inl (0, 12)) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedTenth_final_pair_q, generatedTenthQSupportCoefficient09]
    push_cast
    rfl
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inl (0, 17)) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedTenth_final_pair_q, generatedTenthQSupportCoefficient10]
    push_cast
    rfl
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inl (0, 98)) = (8 : ℝ) / 128
    rw [generatedTenth_final_pair_q, generatedTenthQSupportCoefficient11]
    push_cast
    rfl
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inr (Sum.inl (generatedTenthSelectedShortOctad 0, 1))) = (4 : ℝ) / 128
    rw [generatedTenth_selected_octad_numerator, generatedTenthQSupportCoefficient12]
    norm_num
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inr (Sum.inl (generatedTenthSelectedShortOctad 1, 1))) = (8 : ℝ) / 128
    rw [generatedTenth_selected_octad_numerator, generatedTenthQSupportCoefficient13]
    norm_num
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inr (Sum.inl (generatedTenthSelectedShortOctad 2, 2))) = ((-8 : ℤ) : ℝ) / 128
    rw [generatedTenth_selected_octad_numerator, generatedTenthQSupportCoefficient14]
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inr (Sum.inl (generatedTenthSelectedShortOctad 3, 0))) = (4 : ℝ) / 128
    rw [generatedTenth_selected_octad_numerator, generatedTenthQSupportCoefficient15]
    norm_num
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inr (Sum.inl (generatedTenthSelectedShortOctad 4, 0))) = (4 : ℝ) / 128
    rw [generatedTenth_selected_octad_numerator, generatedTenthQSupportCoefficient16]
    norm_num
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inr (Sum.inl (generatedTenthSelectedShortOctad 5, 0))) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedTenth_selected_octad_numerator, generatedTenthQSupportCoefficient17]
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inr (Sum.inl (generatedTenthSelectedShortOctad 6, 0))) = ((-12 : ℤ) : ℝ) / 128
    rw [generatedTenth_selected_octad_numerator, generatedTenthQSupportCoefficient18]
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inr (Sum.inl (generatedTenthSelectedShortOctad 7, 1))) = (4 : ℝ) / 128
    rw [generatedTenth_selected_octad_numerator, generatedTenthQSupportCoefficient19]
    norm_num
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inr (Sum.inl (generatedTenthSelectedShortOctad 8, 0))) = (4 : ℝ) / 128
    rw [generatedTenth_selected_octad_numerator, generatedTenthQSupportCoefficient20]
    norm_num
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inr (Sum.inl (generatedTenthSelectedShortOctad 9, 2))) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedTenth_selected_octad_numerator, generatedTenthQSupportCoefficient21]
  · change (griessConwayEncode generatedTenthAxis).2.1
        (Sum.inr (Sum.inl (generatedTenthSelectedShortOctad 10, 0))) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedTenth_selected_octad_numerator, generatedTenthQSupportCoefficient22]

/-- Every selected original physical short coordinate has an actual nonzero coefficient. -/
theorem generatedTenth_Q_support_nonzero (j : Fin 23) :
    (griessConwayEncode generatedTenthAxis).2.1 (generatedTenthQSupportIndex j) ≠ 0 := by
  rw [generatedTenth_Q_support_coordinate]
  exact div_ne_zero (by exact_mod_cast generatedTenth_Q_support_numerator_ne_zero j)
    (by norm_num)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
