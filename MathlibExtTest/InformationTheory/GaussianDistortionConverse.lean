/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.GaussianDistortionConverse

@[expose] public section

open MathlibExt.InformationTheory.GaussianDistortionConverse
  MathlibExt.InformationTheory.GaussianDistortionFeasibility
open scoped ENNReal NNReal

namespace MathlibExtTest.InformationTheory.GaussianDistortionConverse

private lemma log_four_eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4, Real.log_pow]
  norm_num

private lemma coe_one_eq : ((1 : ℝ≥0) : ℝ) = 1 := by norm_num

private lemma coe_four_eq : ((4 : ℝ≥0) : ℝ) = 4 := by norm_num

/-- At the zero pair the test with variances `1` and `4` is `log 2`. -/
example : gaussianTest 1 4 (0, 0) = Real.log 2 := by
  rw [gaussianTest_zero_zero 1 4 (by norm_num) (by norm_num), coe_four_eq, coe_one_eq,
    div_one, log_four_eq]
  ring

/-- At the pair `(2, 1)` with variances `1` and `4` the two quadratic
terms cancel, and the test is again `log 2`. -/
example : gaussianTest 1 4 (2, 1) = Real.log 2 := by
  rw [gaussianTest_eq 1 4 (by norm_num) (by norm_num) (2, 1), coe_four_eq, coe_one_eq,
    div_one, log_four_eq]
  norm_num

/-- The exponentiated test value at the zero pair is `2`. -/
example : Real.exp (gaussianTest 1 4 (0, 0)) = 2 := by
  have h1 : gaussianTest 1 4 (0, 0) = Real.log 2 := by
    rw [gaussianTest_zero_zero 1 4 (by norm_num) (by norm_num), coe_four_eq, coe_one_eq,
      div_one, log_four_eq]
    ring
  rw [h1, Real.exp_log (by norm_num)]

/-- Concrete rate-distortion lower bound: at source variance `4` and
distortion `1`, the rate-distortion function is at least one bit. -/
example : ENNReal.ofReal 1 ≤ rateDistortion 4 ((1 : ℝ≥0) : ℝ) := by
  have h := rateDistortion_ge_ofReal_log_div 4 1 (by norm_num) (by norm_num)
  have hlog : Real.log (((4 : ℝ≥0) : ℝ) / ((1 : ℝ≥0) : ℝ)) / (2 * Real.log 2) = 1 := by
    rw [coe_four_eq, coe_one_eq, div_one, log_four_eq]
    exact div_self (mul_ne_zero (by norm_num) (Real.log_pos (by norm_num)).ne')
  rw [hlog] at h
  exact h

end MathlibExtTest.InformationTheory.GaussianDistortionConverse
