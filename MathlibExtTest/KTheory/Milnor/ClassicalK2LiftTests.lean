/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.ZMod.Basic
import MathlibExt.KTheory.Milnor.ClassicalK2Laws
import MathlibExt.KTheory.Milnor.ClassicalK2Lift

/-! A concrete client of the classical Milnor `K₂` lift, using the sign symbol over `ℚ`. -/

open MilnorK

private def negativeBit (unit : ℚˣ) : ZMod 2 :=
  if (unit : ℚ) < 0 then 1 else 0

private theorem negativeBit_mul (left right : ℚˣ) :
    negativeBit (left * right) = negativeBit left + negativeBit right := by
  have leftCases := lt_or_gt_of_ne (Units.ne_zero left)
  have rightCases := lt_or_gt_of_ne (Units.ne_zero right)
  simp only [negativeBit, Units.val_mul]
  rcases leftCases with leftNeg | leftPos <;> rcases rightCases with rightNeg | rightPos
  · rw [ite_eq_right (not_lt_of_gt (mul_pos_of_neg_of_neg leftNeg rightNeg)),
      ite_eq_left leftNeg, ite_eq_left rightNeg]; decide
  · rw [ite_eq_left (mul_neg_of_neg_of_pos leftNeg rightPos),
      ite_eq_left leftNeg, ite_eq_right (not_lt_of_gt rightPos)]; decide
  · rw [ite_eq_left (mul_neg_of_pos_of_neg leftPos rightNeg),
      ite_eq_right (not_lt_of_gt leftPos), ite_eq_left rightNeg]; decide
  · rw [ite_eq_right (not_lt_of_gt (mul_pos leftPos rightPos)),
      ite_eq_right (not_lt_of_gt leftPos), ite_eq_right (not_lt_of_gt rightPos)]; decide

private def signBimap : SteinbergBimap ℚ (ZMod 2) where
  toFun left right := negativeBit left * negativeBit right
  map_mul_left left₁ left₂ right := by rw [negativeBit_mul, add_mul]
  map_mul_right left right₁ right₂ := by rw [negativeBit_mul, mul_add]
  steinberg value _ _ := by
    change ((if value < 0 then 1 else 0 : ZMod 2) *
      (if 1 - value < 0 then 1 else 0)) = 0
    by_cases negative : value < 0
    · have complementPos : 0 < 1 - value :=
        sub_pos.mpr (lt_trans negative zero_lt_one)
      rw [ite_eq_right (not_lt_of_gt complementPos), mul_zero]
    · rw [ite_eq_right negative, zero_mul]

private def negativeTwo : ℚˣ := Units.mk0 (-2) (by decide)

-- The two inputs are negative rational units, and the target value is nonzero.
example : liftK2OfBimap signBimap (k2Symbol ℚ (-1) negativeTwo⁻¹) = 1 := by
  rw [k2Symbol_inv_right, map_neg, liftK2OfBimap_k2Symbol]
  change -(negativeBit (-1 : ℚˣ) * negativeBit negativeTwo) = 1
  have minusOne : negativeBit (-1 : ℚˣ) = 1 :=
    ite_eq_left (show ((-1 : ℚˣ) : ℚ) < 0 from by decide)
  have minusTwo : negativeBit negativeTwo = 1 :=
    ite_eq_left (show (negativeTwo : ℚ) < 0 from by decide)
  rw [minusOne, minusTwo]; decide
