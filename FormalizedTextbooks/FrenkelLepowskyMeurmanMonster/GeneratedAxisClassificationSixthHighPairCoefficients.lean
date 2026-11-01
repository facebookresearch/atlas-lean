/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPairCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPairZero

/-! The original high short coefficients occur exactly on pairs containing coordinate zero. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original pair coefficient has its actual signed quarter normalization. -/
theorem generatedSixth_original_pair_coordinate (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedOddAxis).2.1 (Sum.inl (s, p)) =
      (if s = 0 then 1 else -1) *
        (if (griessCoordinatePair p).1 = 0 ∨ (griessCoordinatePair p).2 = 0
          then -3 else 1) / 4 := by
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have hm : golayEncodedMask 0 = 0 := by decide +kernel
  have hn := griessCoordinatePair_ne p
  rw [generatedOddAxis, generatedAxis_triality_odd_pair_coordinate]
  simp only [griessShortVector, griessShortIntegral, Fin.val_zero, hm,
    Nat.zero_testBit, Bool.false_eq_true, ite_false]
  by_cases ha : (griessCoordinatePair p).1 = 0
  · have hb : (griessCoordinatePair p).2 ≠ 0 := by
      intro hb
      exact hn (ha.trans hb.symm)
    simp only [ha, hb, ite_true, ite_false, true_or]
    split_ifs <;> norm_num <;> field_simp <;> nlinarith only [hs]
  · by_cases hb : (griessCoordinatePair p).2 = 0
    · simp only [ha, hb, ite_true, ite_false, or_true]
      split_ifs <;> norm_num <;> field_simp <;> nlinarith only [hs]
    · simp only [ha, hb, ite_false, or_false]
      split_ifs <;> norm_num <;> field_simp <;> nlinarith only [hs]

/-- Away from coordinate zero the genuine original short coefficients have square one sixteenth. -/
theorem generatedSixth_original_pair_small (s : Fin 2) (p : Fin 276)
    (ha : (griessCoordinatePair p).1 ≠ 0) (hb : (griessCoordinatePair p).2 ≠ 0) :
    ((griessConwayEncode generatedOddAxis).2.1 (Sum.inl (s, p))) ^ 2 =
      (1 / 16 : ℝ) := by
  rw [generatedSixth_original_pair_coordinate]
  simp only [ha, hb, false_or, ite_false]
  split_ifs <;> norm_num

/-- The original quarter coefficients, including their high pair rows, are all bounded. -/
theorem generatedSixth_original_short_square_bound (r : GriessShortIndex) :
    ((griessConwayEncode generatedOddAxis).2.1 r) ^ 2 ≤ (9 / 16 : ℝ) := by
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

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
