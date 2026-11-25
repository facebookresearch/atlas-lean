/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Crypto.Privacy.Gaussian

/-!
# Gaussian tail and calibration tests

Tests for the Gaussian tail bound `gaussianReal_Ioi_le_half_exp` and the
calibration lemma `gaussian_calibration_tail_le`.
-/

@[expose] public section

namespace Cslib.Crypto.PrivacyTests

open MeasureTheory ProbabilityTheory Cslib.Crypto.Privacy

open scoped ENNReal

theorem test_gaussianReal_Ioi_zero_le : gaussianReal 0 1 (Set.Ioi 0) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
  have h := gaussianReal_Ioi_le_half_exp (u := (0 : ℝ)) le_rfl
  rw [show (-(0 : ℝ) ^ 2 / 2) = 0 by norm_num, Real.exp_zero] at h
  exact h

theorem test_gaussianReal_Ioi_one_le : gaussianReal 0 1 (Set.Ioi 1) ≤ ENNReal.ofReal (Real.exp (-(1 : ℝ) ^ 2 / 2) / 2) :=
  gaussianReal_Ioi_le_half_exp (by norm_num)

theorem test_gaussian_calibration_main_branch : gaussianReal 0 1 (Set.Ioi (3 / 4 : ℝ)) ≤ ENNReal.ofReal (99 / 100 : ℝ) := by
  have hlog : Real.log ((5 / 4 : ℝ) / (99 / 100)) ≤ 26 / 99 := by
    have h :=
      Real.log_le_sub_one_of_pos (show (0 : ℝ) < (5 / 4) / (99 / 100) by norm_num)
    have hfrac : ((5 / 4 : ℝ) / (99 / 100)) - 1 = 26 / 99 := by norm_num
    linarith
  have hc : 2 * Real.log ((5 / 4 : ℝ) / (99 / 100)) < (1 : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ^ 2 = 1 := by norm_num
    rw [h1]
    linarith
  have h :=
    gaussian_calibration_tail_le (ε := (1 / 2 : ℝ)) (δ := (99 / 100 : ℝ))
      (c := (1 : ℝ)) (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hc (by norm_num) (by norm_num)
  have hth : ((1 / 2 : ℝ) / (1 / 2) - (1 / 2) / 2) = 3 / 4 := by norm_num
  rwa [hth] at h

theorem test_gaussian_calibration_s_neg_branch : gaussianReal 0 1 (Set.Ioi (-1 / 140 : ℝ)) ≤ ENNReal.ofReal (99 / 100 : ℝ) := by
  have hexp : (125 / 99 : ℝ) < Real.exp (49 / 200) := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 49 / 200 by norm_num)
    have hnum : (125 / 99 : ℝ) < 1 + 49 / 200 + (49 / 200) ^ 2 / 2 := by norm_num
    linarith
  have hlog : Real.log (125 / 99 : ℝ) < 49 / 200 := by
    have h := Real.log_lt_log (show (0 : ℝ) < 125 / 99 by norm_num) hexp
    rwa [Real.log_exp] at h
  have hfrac : ((5 / 4 : ℝ) / (99 / 100)) = 125 / 99 := by norm_num
  have hc : 2 * Real.log ((5 / 4 : ℝ) / (99 / 100)) < (7 / 10 : ℝ) ^ 2 := by
    rw [hfrac]
    have hsq : (7 / 10 : ℝ) ^ 2 = 49 / 100 := by norm_num
    rw [hsq]
    linarith
  have h :=
    gaussian_calibration_tail_le (ε := (99 / 100 : ℝ)) (δ := (99 / 100 : ℝ))
      (c := (7 / 10 : ℝ)) (r := (99 / 70 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hc (by norm_num) (by norm_num)
  have hth : ((99 / 100 : ℝ) / (99 / 70) - (99 / 70) / 2) = -1 / 140 := by norm_num
  rwa [hth] at h

theorem test_gaussian_calibration_delta_ge_one : gaussianReal 0 1 (Set.Ioi (3 / 4 : ℝ)) ≤ ENNReal.ofReal (2 : ℝ) := by
  have hlog : Real.log ((5 / 4 : ℝ) / 2) ≤ 0 :=
    Real.log_nonpos (by norm_num) (by norm_num)
  have hc : 2 * Real.log ((5 / 4 : ℝ) / 2) < (1 : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ^ 2 = 1 := by norm_num
    rw [h1]
    linarith
  have h :=
    gaussian_calibration_tail_le (ε := (1 / 2 : ℝ)) (δ := (2 : ℝ)) (c := (1 : ℝ))
      (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hc (by norm_num) (by norm_num)
  have hth : ((1 / 2 : ℝ) / (1 / 2) - (1 / 2) / 2) = 3 / 4 := by norm_num
  rwa [hth] at h

#print axioms ProbabilityTheory.gaussianReal_Ioi_le_half_exp
#print axioms Cslib.Crypto.Privacy.gaussian_calibration_tail_le

end Cslib.Crypto.PrivacyTests
