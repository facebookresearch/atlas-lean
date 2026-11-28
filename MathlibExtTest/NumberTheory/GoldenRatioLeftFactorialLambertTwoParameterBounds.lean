/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.ExponentialBounds
import MathlibExt.NumberTheory.GoldenRatioLeftFactorialLambertKurepaPartialIntegralLambertSequenceBounds
import MathlibExt.NumberTheory.GoldenRatioLeftFactorialLambertTwoParameterBounds

/-! # Tests for the two-parameter Lambert bounds -/

namespace MathlibExtTest.NumberTheory.GoldenRatioLeftFactorialLambertTwoParameterBounds

open MetaMathlibExt Real

-- The lower-branch comparison includes the endpoint `-1`.
example : lambertMap (-1) < lambertMap (-2) :=
  lambertMap_strictAntiOn_Iic (by norm_num [Set.mem_Iic]) (by norm_num [Set.mem_Iic])
    (by norm_num)

-- At `n = 3`, the cutoff `2` normalizes to a target other than `4 / 7`.
example : (2 : ℝ) ^ (2 : ℕ) * exp (-2) = (2 * exp (-1)) ^ (2 : ℕ) := by
  have hroot : ((2 * exp (-1)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = 2 * exp (-1) := by
    rw [show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num]
    exact pow_rpow_inv_natCast (by positivity) (by decide)
  have h := lambertCutoff_pow_mul_exp 3 (by decide) 2
    (c := (2 * exp (-1)) ^ (2 : ℕ)) (by positivity) (by
      rw [show ((3 : ℕ) : ℝ) - 1 = 2 by norm_num, hroot,
        show -(2 : ℝ) / 2 = -1 by norm_num, lambertMap.eq_def]
      ring)
  exact h

-- At the smallest allowed `n` and `m`, the actual lower-branch cutoff puts the integral in (33, 34).
example : ∃ A : ℝ, 4 ≤ A ∧
    lambertMap (-A / 4) = -(1 / 4) * (4 / 7 : ℝ) ^ (1 / 4 : ℝ) ∧
    kurepaPartialIntegral 5 A ∈ Set.Ioo 33 34 := by
  obtain ⟨A, hA, hW⟩ := exists_lambertSequence (n := 5) (by decide)
    (c := 4 / 7) (by norm_num) (by norm_num)
  have hb := kurepaPartialIntegral_lambertSequence_two_bounds 5 1 (by decide) le_rfl A hA
    (by norm_num at hW ⊢; exact hW)
  rw [show ((5 : ℕ) : ℝ) - 1 = 4 by norm_num] at hA hW
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  exact ⟨A, hA, hW, by linarith [hb.2], hb.1⟩

-- Doubling `m` gives an actual cutoff with integral in the narrower interval (33.5, 34).
example : ∃ A : ℝ, 4 ≤ A ∧
    lambertMap (-A / 4) = -(1 / 4) * (4 / 14 : ℝ) ^ (1 / 4 : ℝ) ∧
    kurepaPartialIntegral 5 A ∈ Set.Ioo (67 / 2) 34 := by
  obtain ⟨A, hA, hW⟩ := exists_lambertSequence (n := 5) (by decide)
    (c := 4 / 14) (by norm_num) (by norm_num)
  have hb := kurepaPartialIntegral_lambertSequence_two_bounds 5 2 (by decide) (by decide) A hA
    (by norm_num at hW ⊢; exact hW)
  rw [show ((5 : ℕ) : ℝ) - 1 = 4 by norm_num] at hA hW
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  exact ⟨A, hA, hW, by linarith [hb.2], hb.1⟩

-- Independent endpoint check for the lower branch: here the comparison is just `2 < exp 1`.
example : lambertMap (-1) < lambertMap (-2) := by
  have h : 2 * exp (-1) < 1 := by
    rw [exp_neg, ← div_eq_mul_inv, div_lt_one (exp_pos _)]
    exact exp_one_gt_two
  rw [lambertMap.eq_def, lambertMap.eq_def, show (-2 : ℝ) = -1 + -1 by norm_num, exp_add]
  nlinarith only [mul_lt_mul_of_pos_right h (exp_pos (-1))]

-- Check both strict endpoints at `n = 5`, `m = 2` without invoking the bounds theorem.
-- Certify `A > 10`, then bound the explicit integral remainder using the cutoff equation.
example : ∃ A : ℝ, 4 ≤ A ∧
    lambertMap (-A / 4) = -(1 / 4) * (4 / 14 : ℝ) ^ (1 / 4 : ℝ) ∧
    kurepaPartialIntegral 5 A ∈ Set.Ioo (67 / 2) 34 := by
  obtain ⟨A, hA, hW⟩ := exists_lambertSequence (n := 5) (by decide)
    (c := 4 / 14) (by norm_num) (by norm_num)
  rw [show ((5 : ℕ) : ℝ) - 1 = 4 by norm_num] at hA hW
  refine ⟨A, hA, hW, ?_⟩
  have h10 : 10 < A := by
    have hexp : exp (5 / 2) < 13 := by
      have he : exp 1 < 11 / 4 := exp_one_lt_d9.trans (by norm_num)
      have hs : exp (5 / 2) ^ (2 : ℕ) < (13 : ℝ) ^ (2 : ℕ) := calc
        _ = exp 1 ^ (5 : ℕ) := by rw [← exp_nat_mul, ← exp_nat_mul]; norm_num
        _ < (11 / 4 : ℝ) ^ (5 : ℕ) := pow_lt_pow_left₀ he (exp_pos _).le (by decide)
        _ < _ := by norm_num
      exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hs
    have hroot : (4 / 14 : ℝ) ^ (1 / 4 : ℝ) < 10 / 13 := calc
      _ < ((10 / 13 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) :=
        rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = _ := by
        rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
        exact pow_rpow_inv_natCast (by norm_num) (by decide)
    have hcut : lambertMap (-(10 : ℝ) / 4) < lambertMap (-A / 4) := by
      have h := mul_lt_mul hroot hexp.le (exp_pos _) (by norm_num : (0 : ℝ) ≤ 10 / 13)
      rw [hW, lambertMap.eq_def, show -(10 : ℝ) / 4 = -(5 / 2) by norm_num, exp_neg,
        ← div_eq_mul_inv, div_lt_iff₀ (exp_pos _)]
      linarith only [h]
    have hArg : -A / 4 ∈ Set.Iic (-1 : ℝ) := by rw [Set.mem_Iic]; linarith
    have hArg10 : -(10 : ℝ) / 4 ∈ Set.Iic (-1 : ℝ) := by norm_num [Set.mem_Iic]
    have h := (lambertMap_strictAntiOn_Iic.lt_iff_gt hArg10 hArg).mp hcut
    linarith
  have hA₀ : 0 < A := by linarith
  have hnorm : A ^ (4 : ℕ) * exp (-A) = 2 / 7 := by
    rw [lambertMap.eq_def] at hW
    have hmul : A * exp (-A / 4) = (4 / 14 : ℝ) ^ (1 / 4 : ℝ) := by
      linear_combination -4 * hW
    have h := congrArg (fun x : ℝ => x ^ (4 : ℕ)) hmul
    rw [mul_pow, ← exp_nat_mul, show ((4 : ℕ) : ℝ) * (-A / 4) = -A by push_cast; ring,
      ← rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 4 / 14)] at h
    norm_num at h ⊢
    exact h
  have hpoly : 34 - kurepaPartialIntegral 5 A =
      exp (-A) * (34 + 33 * A + 16 * A ^ 2 + 5 * A ^ 3 + A ^ 4) := by
    have h := sum_factorial_sub_kurepaPartialIntegral 5 A
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linear_combination h
  have hrem : 34 - kurepaPartialIntegral 5 A =
      (2 / 7) * (34 / A ^ 4 + 33 / A ^ 3 + 16 / A ^ 2 + 5 / A + 1) := by
    have he : exp (-A) = (2 / 7) / A ^ (4 : ℕ) :=
      (eq_div_iff (pow_ne_zero _ hA₀.ne')).mpr (by simpa only [mul_comm] using hnorm)
    rw [hpoly, he]
    field_simp [hA₀.ne']
  have hlt : 34 - kurepaPartialIntegral 5 A < 1 / 2 := calc
    _ ≤ (2 / 7 : ℝ) * (34 / 10 ^ 4 + 33 / 10 ^ 3 + 16 / 10 ^ 2 + 5 / 10 + 1) := by
      rw [hrem]
      gcongr
    _ < _ := by norm_num
  have hpos : 0 < 34 - kurepaPartialIntegral 5 A := by rw [hrem]; positivity
  exact ⟨by linarith only [hlt], by linarith only [hpos]⟩

end MathlibExtTest.NumberTheory.GoldenRatioLeftFactorialLambertTwoParameterBounds
