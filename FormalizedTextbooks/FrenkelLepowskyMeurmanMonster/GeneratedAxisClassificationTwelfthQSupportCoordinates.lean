/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthQSupportData

/-! Every selected original quotient witness has a genuine nonzero full-axis short coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual full-axis coefficient of each selected original physical short witness. -/
theorem generatedTwelfth_Q_support_coordinate (j : Fin 23) :
    (griessConwayEncode generatedTwelfthAxis).2.1 (generatedTwelfthQSupportIndex j) =
      (generatedTwelfthQSupportNumerator j : ℝ) / 128 := by
  fin_cases j
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inl (0, 0)) = ((-8 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_final_pair_q, generatedTwelfthQSupportCoefficient00]
    push_cast
    rfl
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inl (1, 0)) = (8 : ℝ) / 128
    rw [generatedTwelfth_final_pair_q, generatedTwelfthQSupportCoefficient01]
    push_cast
    rfl
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inl (0, 1)) = ((-8 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_final_pair_q, generatedTwelfthQSupportCoefficient02]
    push_cast
    rfl
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inl (0, 2)) = ((-8 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_final_pair_q, generatedTwelfthQSupportCoefficient03]
    push_cast
    rfl
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inl (0, 15)) = (8 : ℝ) / 128
    rw [generatedTwelfth_final_pair_q, generatedTwelfthQSupportCoefficient04]
    push_cast
    rfl
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inl (0, 16)) = ((-8 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_final_pair_q, generatedTwelfthQSupportCoefficient05]
    push_cast
    rfl
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inl (0, 17)) = ((-8 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_final_pair_q, generatedTwelfthQSupportCoefficient06]
    push_cast
    rfl
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inl (0, 86)) = ((-8 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_final_pair_q, generatedTwelfthQSupportCoefficient07]
    push_cast
    rfl
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inl (0, 101)) = (8 : ℝ) / 128
    rw [generatedTwelfth_final_pair_q, generatedTwelfthQSupportCoefficient08]
    push_cast
    rfl
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad 0, 0))) = ((-8 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_selected_octad_numerator, generatedTwelfthQSupportCoefficient09]
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad 1, 4))) = (8 : ℝ) / 128
    rw [generatedTwelfth_selected_octad_numerator, generatedTwelfthQSupportCoefficient10]
    norm_num
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad 2, 3))) = ((-8 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_selected_octad_numerator, generatedTwelfthQSupportCoefficient11]
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad 3, 4))) = ((-8 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_selected_octad_numerator, generatedTwelfthQSupportCoefficient12]
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad 4, 0))) = ((-8 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_selected_octad_numerator, generatedTwelfthQSupportCoefficient13]
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad 5, 0))) = (8 : ℝ) / 128
    rw [generatedTwelfth_selected_octad_numerator, generatedTwelfthQSupportCoefficient14]
    norm_num
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad 5, 3))) = ((-8 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_selected_octad_numerator, generatedTwelfthQSupportCoefficient15]
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad 6, 0))) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_selected_octad_numerator, generatedTwelfthQSupportCoefficient16]
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad 6, 2))) = (4 : ℝ) / 128
    rw [generatedTwelfth_selected_octad_numerator, generatedTwelfthQSupportCoefficient17]
    norm_num
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad 7, 0))) = (4 : ℝ) / 128
    rw [generatedTwelfth_selected_octad_numerator, generatedTwelfthQSupportCoefficient18]
    norm_num
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad 8, 0))) = ((-12 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_selected_octad_numerator, generatedTwelfthQSupportCoefficient19]
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad 9, 0))) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_selected_octad_numerator, generatedTwelfthQSupportCoefficient20]
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad 10, 1))) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_selected_octad_numerator, generatedTwelfthQSupportCoefficient21]
  · change (griessConwayEncode generatedTwelfthAxis).2.1
        (Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad 11, 0))) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedTwelfth_selected_octad_numerator, generatedTwelfthQSupportCoefficient22]

/-- Every selected original physical short coordinate has an actual nonzero coefficient. -/
theorem generatedTwelfth_Q_support_nonzero (j : Fin 23) :
    (griessConwayEncode generatedTwelfthAxis).2.1 (generatedTwelfthQSupportIndex j) ≠ 0 := by
  rw [generatedTwelfth_Q_support_coordinate]
  exact div_ne_zero (by exact_mod_cast generatedTwelfth_Q_support_numerator_ne_zero j)
    (by norm_num)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
