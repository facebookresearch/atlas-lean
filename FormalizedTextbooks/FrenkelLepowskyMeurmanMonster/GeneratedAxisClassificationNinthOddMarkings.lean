/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOddMarkingCertificates

/-! The literal original axis has the specified128 large odd-short rows, once every original
 integer dictionary packet has been checked. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The absolute odd-short coefficient is the checked original numerator divided by64. -/
theorem generatedNinth_final_odd_numeric_abs (d : Fin 2048) (i : Fin 24) :
    |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inr (d, i)))| =
      ((|generatedNinthFinalOddNumerator d i| : ℤ) : ℝ) / 64 := by
  have hs : |qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)| = 1 := by
    unfold qSign
    split_ifs <;> norm_num
  rw [generatedNinth_final_odd_numeric, abs_div, abs_mul, hs, one_mul]
  norm_num [Int.cast_abs]

/-- Every displayed odd marking has actual coefficient of absolute value one eighth. -/
theorem generatedNinth_final_odd_marking_coefficient (d : Fin 2048) (i : Fin 24)
    (h : (d, i) ∈ generatedNinthOddMarkings) :
    |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inr (d, i)))| = (1 / 8 : ℝ) := by
  rw [generatedNinth_final_odd_numeric_abs,
    (generatedNinth_odd_marking_integer_certificate d i).1.mpr h]
  norm_num

/-- Every other actual preferred odd row has absolute coefficient at most one thirty-second. -/
theorem generatedNinth_final_odd_nonmarking_bound (d : Fin 2048) (i : Fin 24)
    (h : (d, i) ∉ generatedNinthOddMarkings) :
    |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inr (d, i)))| ≤ (1 / 32 : ℝ) := by
  have hi := (generatedNinth_odd_marking_integer_certificate d i).2 h
  have hr : ((|generatedNinthFinalOddNumerator d i| : ℤ) : ℝ) ≤ 2 := by
    exact_mod_cast hi
  rw [generatedNinth_final_odd_numeric_abs]
  linarith

/-- The large actual odd coefficients occur exactly at the128 displayed preferred
dictionary labels. -/
theorem generatedNinth_final_odd_marking_iff (d : Fin 2048) (i : Fin 24) :
    |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inr (d, i)))| = (1 / 8 : ℝ) ↔
      (d, i) ∈ generatedNinthOddMarkings := by
  constructor
  · intro h
    rw [generatedNinth_final_odd_numeric_abs] at h
    have hr : ((|generatedNinthFinalOddNumerator d i| : ℤ) : ℝ) = 8 := by linarith
    have hi : |generatedNinthFinalOddNumerator d i| = 8 := by exact_mod_cast hr
    exact (generatedNinth_odd_marking_integer_certificate d i).1.mp hi
  · exact generatedNinth_final_odd_marking_coefficient d i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
