/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
public import CSLibExt.MachineLearning.DepthSeparationConstruction

open Cslib.MachineLearning.DepthSeparation

/-! Value tests for the iterated tent map network: one-step values,
multistep sequences, the out-of-range boundary case, network values
through the construction theorem, and `#print axioms` checks. -/
namespace CSLibExtTest.MachineLearning.DepthSeparationConstruction

theorem tent_zero : tent (0 : ℝ) = 0 := tent_eq_zero_of_nonpos 0 le_rfl

theorem tent_quarter : tent (1 / 4 : ℝ) = 1 / 2 := by
  rw [tent_eq_two_mul (1 / 4) (by norm_num) (by norm_num)]; norm_num

theorem tent_half : tent (1 / 2 : ℝ) = 1 := by
  rw [tent_eq_two_mul (1 / 2) (by norm_num) (by norm_num)]; norm_num

theorem tent_three_quarters : tent (3 / 4 : ℝ) = 1 / 2 := by
  rw [tent_eq_two_sub (3 / 4) (by norm_num) (by norm_num)]; norm_num

theorem tent_one : tent (1 : ℝ) = 0 := tent_eq_zero_of_ge_one 1 le_rfl

theorem tent_neg_one : tent (-1 : ℝ) = 0 :=
  tent_eq_zero_of_nonpos (-1) (by norm_num)

theorem tent_two : tent (2 : ℝ) = 0 := tent_eq_zero_of_ge_one 2 (by norm_num)

theorem tentIter_two_quarter : tentIter 2 (1 / 4 : ℝ) = 1 := by
  show tentIter (1 + 1) (1 / 4 : ℝ) = 1
  rw [tentIter_succ, tent_quarter]
  show tentIter (0 + 1) (1 / 2 : ℝ) = 1
  rw [tentIter_succ, tentIter_zero]
  exact tent_half

theorem tentIter_two_half : tentIter 2 (1 / 2 : ℝ) = 0 := by
  show tentIter (1 + 1) (1 / 2 : ℝ) = 0
  rw [tentIter_succ, tent_half]
  show tentIter (0 + 1) (1 : ℝ) = 0
  rw [tentIter_succ, tentIter_zero]
  exact tent_one

theorem tentIter_two_three_quarters : tentIter 2 (3 / 4 : ℝ) = 1 := by
  show tentIter (1 + 1) (3 / 4 : ℝ) = 1
  rw [tentIter_succ, tent_three_quarters]
  show tentIter (0 + 1) (1 / 2 : ℝ) = 1
  rw [tentIter_succ, tentIter_zero]
  exact tent_half

theorem tentIter_two_zero : tentIter 2 (0 : ℝ) = 0 := by
  show tentIter (1 + 1) (0 : ℝ) = 0
  rw [tentIter_succ, tent_zero]
  show tentIter (0 + 1) (0 : ℝ) = 0
  rw [tentIter_succ, tentIter_zero]
  exact tent_zero

theorem tentIter_one_five_quarters : tentIter 1 (5 / 4 : ℝ) = 0 := by
  show tentIter (0 + 1) (5 / 4 : ℝ) = 0
  rw [tentIter_succ, tentIter_zero]
  exact tent_eq_zero_of_ge_one (5 / 4) (by norm_num)

theorem tent_fract_five_quarters :
    tent (Int.fract ((2 : ℝ) ^ 0 * (5 / 4))) = 1 / 2 := by
  simp only [pow_zero, one_mul]
  have h54 : (5 / 4 : ℝ) = 1 + 1 / 4 := by norm_num
  have hfr : Int.fract (1 / 4 : ℝ) = 1 / 4 :=
    Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  rw [h54, Int.fract_one_add, hfr]
  exact tent_quarter

theorem m1_fails_outside :
    tentIter 1 (5 / 4 : ℝ) ≠ tent (Int.fract ((2 : ℝ) ^ 0 * (5 / 4))) := by
  rw [tentIter_one_five_quarters, tent_fract_five_quarters]; norm_num

theorem net_two_quarter :
    (tentNet.forward 2 (single (1 / 4 : ℝ))) 0 = 1 / 2 := by
  show (tentNet.forward (2 * 1) (single (1 / 4 : ℝ))) 0 = 1 / 2
  rw [tentNet_forward]
  show tentIter (0 + 1) (1 / 4 : ℝ) = 1 / 2
  rw [tentIter_succ, tentIter_zero]
  exact tent_quarter

theorem net_four_quarter :
    (tentNet.forward 4 (single (1 / 4 : ℝ))) 0 = 1 := by
  show (tentNet.forward (2 * 2) (single (1 / 4 : ℝ))) 0 = 1
  rw [tentNet_forward]
  exact tentIter_two_quarter

#print axioms tentIter_succ_eq_tent_fract
#print axioms tentNet_forward

end CSLibExtTest.MachineLearning.DepthSeparationConstruction
