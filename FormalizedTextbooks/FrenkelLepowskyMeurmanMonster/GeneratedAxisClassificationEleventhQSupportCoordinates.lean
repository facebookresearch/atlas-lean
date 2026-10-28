/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhQSupportData

/-! Every selected original quotient witness has a genuine nonzero full-axis short coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual full-axis coefficient of each selected original physical short witness. -/
theorem generatedEleventh_Q_support_coordinate (j : Fin 21) :
    (griessConwayEncode generatedEleventhAxis).2.1 (generatedEleventhQSupportIndex j) =
      (generatedEleventhQSupportNumerator j : ℝ) / 128 := by
  fin_cases j
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inl (0, 0)) = ((-12 : ℤ) : ℝ) / 128
    rw [generatedEleventh_final_pair_q, generatedEleventhQSupportCoefficient00]
    push_cast
    rfl
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inl (1, 0)) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedEleventh_final_pair_q, generatedEleventhQSupportCoefficient01]
    push_cast
    rfl
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inl (0, 1)) = (4 : ℝ) / 128
    rw [generatedEleventh_final_pair_q, generatedEleventhQSupportCoefficient02]
    push_cast
    rfl
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inl (0, 2)) = (4 : ℝ) / 128
    rw [generatedEleventh_final_pair_q, generatedEleventhQSupportCoefficient03]
    push_cast
    rfl
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inl (0, 3)) = (4 : ℝ) / 128
    rw [generatedEleventh_final_pair_q, generatedEleventhQSupportCoefficient04]
    push_cast
    rfl
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inl (0, 4)) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedEleventh_final_pair_q, generatedEleventhQSupportCoefficient05]
    push_cast
    rfl
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inl (0, 5)) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedEleventh_final_pair_q, generatedEleventhQSupportCoefficient06]
    push_cast
    rfl
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inl (0, 15)) = (4 : ℝ) / 128
    rw [generatedEleventh_final_pair_q, generatedEleventhQSupportCoefficient07]
    push_cast
    rfl
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inl (0, 16)) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedEleventh_final_pair_q, generatedEleventhQSupportCoefficient08]
    push_cast
    rfl
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inl (0, 17)) = (4 : ℝ) / 128
    rw [generatedEleventh_final_pair_q, generatedEleventhQSupportCoefficient09]
    push_cast
    rfl
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inl (0, 19)) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedEleventh_final_pair_q, generatedEleventhQSupportCoefficient10]
    push_cast
    rfl
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inr (Sum.inl (generatedEleventhSelectedShortOctad 0, 0))) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedEleventh_selected_octad_numerator, generatedEleventhQSupportCoefficient11]
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inr (Sum.inl (generatedEleventhSelectedShortOctad 1, 0))) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedEleventh_selected_octad_numerator, generatedEleventhQSupportCoefficient12]
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inr (Sum.inl (generatedEleventhSelectedShortOctad 2, 0))) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedEleventh_selected_octad_numerator, generatedEleventhQSupportCoefficient13]
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inr (Sum.inl (generatedEleventhSelectedShortOctad 3, 16))) = (4 : ℝ) / 128
    rw [generatedEleventh_selected_octad_numerator, generatedEleventhQSupportCoefficient14]
    norm_num
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inr (Sum.inl (generatedEleventhSelectedShortOctad 4, 16))) = (4 : ℝ) / 128
    rw [generatedEleventh_selected_octad_numerator, generatedEleventhQSupportCoefficient15]
    norm_num
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inr (Sum.inl (generatedEleventhSelectedShortOctad 5, 0))) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedEleventh_selected_octad_numerator, generatedEleventhQSupportCoefficient16]
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inr (Sum.inl (generatedEleventhSelectedShortOctad 6, 0))) = (4 : ℝ) / 128
    rw [generatedEleventh_selected_octad_numerator, generatedEleventhQSupportCoefficient17]
    norm_num
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inr (Sum.inl (generatedEleventhSelectedShortOctad 7, 0))) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedEleventh_selected_octad_numerator, generatedEleventhQSupportCoefficient18]
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inr (Sum.inl (generatedEleventhSelectedShortOctad 8, 0))) = ((-4 : ℤ) : ℝ) / 128
    rw [generatedEleventh_selected_octad_numerator, generatedEleventhQSupportCoefficient19]
  · change (griessConwayEncode generatedEleventhAxis).2.1
        (Sum.inr (Sum.inl (generatedEleventhSelectedShortOctad 9, 16))) = ((-12 : ℤ) : ℝ) / 128
    rw [generatedEleventh_selected_octad_numerator, generatedEleventhQSupportCoefficient20]

/-- Every selected original physical short coordinate has an actual nonzero coefficient. -/
theorem generatedEleventh_Q_support_nonzero (j : Fin 21) :
    (griessConwayEncode generatedEleventhAxis).2.1 (generatedEleventhQSupportIndex j) ≠ 0 := by
  rw [generatedEleventh_Q_support_coordinate]
  exact div_ne_zero (by exact_mod_cast generatedEleventh_Q_support_numerator_ne_zero j)
    (by norm_num)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
