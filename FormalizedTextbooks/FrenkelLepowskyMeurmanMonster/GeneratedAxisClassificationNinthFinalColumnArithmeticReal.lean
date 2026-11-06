/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmetic

/-! The integer XYZ formula has the original real source signs on both Omega rows. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Integer XYZ arithmetic embeds with both original real dictionary signs retained. -/
theorem generatedNinth_final_column_arithmetic_real (t : SpinIndex) :
    (generatedNinthFinalColumnArithmetic (nortonUIntegerLabel t) : ℝ) =
      4 * qSign (t 11) *
        (if (golayEncodedMask (spinDictionaryCode t).val).testBit 1 then -1 else 1) *
        (generatedNinthIncomingCoefficient (spinDictionaryCode t) : ℝ) +
      (if (golayEncodedMask (spinDictionaryCode t).val).testBit 1 then -1 else 1) *
        qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) *
        ((generatedNinthColumnSpinData 9
          ⟨(spinDictionaryCode t).val, by omega⟩ : ℝ) -
        (generatedNinthColumnSpinData 9
          ⟨(spinDictionaryCode t).val + 2048, by omega⟩ : ℝ)) := by
  obtain h | h := spinDictionaryIndex_cases t
  · rw [h]
    simp only [nortonUIntegerLabel_coeff, spinDictionaryCode_low, golayLabel_low_last,
      qSign_zero, mul_one]
    simp only [generatedNinthFinalColumnArithmetic,
      Nat.mod_eq_of_lt (spinDictionaryCode t).isLt, (spinDictionaryCode t).isLt,
      ite_true, Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_ite, Int.cast_ofNat,
      Int.cast_neg, Int.cast_one, nortonUIntegerSign_real]
  · rw [h]
    simp only [nortonUIntegerLabel_coeff, spinDictionaryCode_high, golayLabel_high_last,
      qSign_one]
    have hm : ((spinDictionaryCode t).val + 2048) % 2048 =
        (spinDictionaryCode t).val := by omega
    have hn : ¬ (spinDictionaryCode t).val + 2048 < 2048 := by omega
    simp only [generatedNinthFinalColumnArithmetic, hm, hn, ite_false,
      Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_ite, Int.cast_ofNat,
      Int.cast_neg, Int.cast_one, nortonUIntegerSign_real]
    split_ifs <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
