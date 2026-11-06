/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthFlag
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagMatrix

/-! The actual matrix watermark is a genuine incident E8-section/short-line flag. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

/-- Original physical coordinates of the genuine phase-selected short line. -/
theorem generatedFourth_flag_short_vector (i : Fin 24) :
    griessShortVector generatedFourthFlagShort i =
      (4 * (if i = 8 then 1 else 0) -
        4 * qSign generatedFourthPairPhase * (if i = 11 then 1 else 0)) / Real.sqrt 8 := by
  have hc : generatedFourthPairPhase = 0 ∨ generatedFourthPairPhase = 1 := by
    have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
    exact h _
  rcases hc with hc | hc
  all_goals
    simp only [generatedFourthFlagShort, generatedFourthFlagSign, hc,
      griessShortVector, griessShortIntegral, generatedFourthPairInput_coordinates]
    norm_num [qSign_zero, qSign_one]
    split_ifs <;> norm_num

/-- The full physical short outer matrix has precisely the two detected coordinates. -/
theorem generatedFourth_flag_outer_entry (i j : Fin 24) :
    griessShortVector generatedFourthFlagShort i * griessShortVector generatedFourthFlagShort j =
      if i = j then (if i = 8 ∨ i = 11 then 2 else 0) else
        if (i = 8 ∧ j = 11) ∨ (i = 11 ∧ j = 8) then
          -2 * qSign generatedFourthPairPhase else 0 := by
  rw [generatedFourth_flag_short_vector, generatedFourth_flag_short_vector,
    div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  split_ifs <;> simp_all <;> nlinarith [qSign_sq generatedFourthPairPhase]

/-- The literal candidate has exactly the flag matrix, with no spectral or class assumption. -/
theorem generatedFourth_matrix_watermark :
    (griessConwayEncode generatedFourthAxis).1 =
      generatedAxisE8ShortFlagMatrix
        (Matrix.diagonal (fun i : Fin 24 => if 4 ≤ i.val ∧ i.val < 12 then 1 else 0))
        (Matrix.vecMulVec (griessShortVector generatedFourthFlagShort)
          (griessShortVector generatedFourthFlagShort)) := by
  ext i j
  simp only [generatedAxisE8ShortFlagMatrix, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Matrix.diagonal_apply,
    Matrix.vecMulVec_apply, generatedFourth_flag_outer_entry]
  by_cases hij : i = j
  · subst j
    rw [generatedFourth_matrix_diagonal]
    simp only [ite_true, generatedFourthProjectionDiagonal]
    by_cases hs : i = 8 ∨ i = 11
    · have hr : 4 ≤ i.val ∧ i.val < 12 := by
        rcases hs with rfl | rfl <;> decide
      norm_num [hs, hr]
    · by_cases hr : 4 ≤ i.val ∧ i.val < 12 <;> norm_num [hs, hr]
  · rw [generatedFourth_matrix_off_diagonal _ _ hij]
    simp only [generatedFourth_pair_coordinates_iff _ _ hij, hij, ite_false]
    split_ifs <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
