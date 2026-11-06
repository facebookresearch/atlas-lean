/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates

/-! Exact rational source coefficients of the original complete odd-axis short packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual rational preferred-pair coefficient in the original source ordering. -/
def generatedAxisGlobalOddShortCoefficientQ (p : GeneratedAxisGlobalOddShortPacketIndex) : ℚ :=
  (if p.1 = 0 then 1 else -1) *
    (if (generatedAxisGlobalPairCoordinates p.2).1 = 0 ∨
        (generatedAxisGlobalPairCoordinates p.2).2 = 0 then -3 else 1) / 4

/-- The rational packet coefficient is exactly the genuine real source coefficient. -/
theorem generatedAxisGlobalOddShortCoefficientQ_actual
    (p : GeneratedAxisGlobalOddShortPacketIndex) :
    (generatedAxisGlobalOddShortCoefficientQ p : ℝ) =
      generatedAxisGlobalOddShortPacketCoefficient p := by
  have hm : golayEncodedMask 0 = 0 := by decide +kernel
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have hn := griessCoordinatePair_ne p.2
  rw [generatedAxisGlobalOddShortCoefficientQ,
    generatedAxisGlobalPairCoordinates_actual]
  simp only [Rat.cast_div, Rat.cast_mul, apply_ite, Rat.cast_neg, Rat.cast_ofNat, generatedAxisGlobalOddShortPacketCoefficient,
    griessShortVector, griessShortIntegral, Fin.val_zero, hm, Nat.zero_testBit,
    Bool.false_eq_true, ite_false]
  by_cases hi : (griessCoordinatePair p.2).1 = 0
  · have hj : (griessCoordinatePair p.2).2 ≠ 0 := by
      intro hj
      exact hn (hi.trans hj.symm)
    simp only [hi, hj, ite_true, ite_false, true_or]
    split_ifs <;> norm_num <;> field_simp <;> nlinarith [hs]
  · by_cases hj : (griessCoordinatePair p.2).2 = 0
    · simp only [hi, hj, ite_true, ite_false, or_true]
      split_ifs <;> norm_num <;> field_simp <;> nlinarith [hs]
    · simp only [hi, hj, ite_false, false_or]
      split_ifs <;> norm_num <;> field_simp <;> nlinarith [hs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
