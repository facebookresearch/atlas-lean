/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.KPellLucasCloseToPowerOfTwo
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Tests for `MathlibExt.NumberTheory.KPellLucasCloseToPowerOfTwo` -/

namespace MathlibExtTest.KPellLucasCloseToPowerOfTwo

open MetaMathlibExt

-- At order one the sum of earlier terms is empty, so each term after index one doubles.
example (n : ℕ) : kPellLucas 1 (n + 2) = 2 * kPellLucas 1 (n + 1) := by
  simpa using kPellLucas_add_two 1 n (by omega)

-- At the least allowed order and index, Q₃ = 14 lies two units below 2⁴.
example : (0.69 : ℝ) * 3 - 1.69 < 4 ∧ (4 : ℝ) < 1.39 * 3 + 3.78 := by
  apply kPellLucas_close_two_pow_exponent_bounds 2 3 4 (by decide) (by decide)
    (by decide) (by decide)
  rw [kPellLucas_two]
  norm_num [pellLucas]

-- The next term is above 2⁵, so the opposite side of the interval and an odd exponent occur.
example : (0.69 : ℝ) * 4 - 1.69 < 5 ∧ (5 : ℝ) < 1.39 * 4 + 3.78 := by
  apply kPellLucas_close_two_pow_exponent_bounds 2 4 5 (by decide) (by decide)
    (by decide) (by decide)
  calc
    _ = (2 : ℝ) ^ (1 : ℝ) := by rw [kPellLucas_two]; norm_num [pellLucas]
    _ < _ := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)

-- Lemma 7 with x = exp 1 and ℓ = 1, where the logarithmic denominator is one.
example : Real.exp 1 < 2 * (5 : ℝ) * Real.log 5 := by
  have hx := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)
  have hTx : Real.exp 1 < 5 := Real.exp_one_lt_three.trans (by norm_num)
  simpa using lt_two_rpow_mul_mul_log_rpow_of_one_lt 1 5 (Real.exp 1)
    (by norm_num) hx (by norm_num) (by simpa using hTx)

-- Test section: with `a = 1 / 2` the constant `-log (1 - a) / a` is `2 log 2`, so Lemma 6 gives
-- `|log (1 + x)| < 2 log 2 · |x|` for `0 < |x| < 1 / 2`.
example (x : ℝ) (hx : |x| < 1 / 2) (hx₀ : x ≠ 0) :
    |Real.log (1 + x)| < 2 * Real.log 2 * |x| := by
  have h := (abs_log_one_add_lt_and_abs_lt_exp_sub_one (1 / 2) x (by norm_num) (by norm_num)
    hx hx₀).1
  have hc : -Real.log (1 - 1 / 2) / (1 / 2) = 2 * Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv]
    ring
  rwa [hc] at h

-- Test section: with `a = 1 / 2`, `e^{-1/2} < 2 / 3` since `e^{1/2} > 3 / 2`, so the constant
-- `a / (1 - e^{-a})` is below `3 / 2` and Lemma 6 gives `|x| < (3 / 2) |eˣ - 1|`.
example (x : ℝ) (hx : |x| < 1 / 2) (hx₀ : x ≠ 0) :
    |x| < 3 / 2 * |Real.exp x - 1| := by
  have h := (abs_log_one_add_lt_and_abs_lt_exp_sub_one (1 / 2) x (by norm_num) (by norm_num)
    hx hx₀).2
  have he : Real.exp (-(1 / 2)) < 2 / 3 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith [Real.add_one_lt_exp (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  have hk : 1 / 2 / (1 - Real.exp (-(1 / 2))) < 3 / 2 := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  exact h.trans_le (mul_le_mul_of_nonneg_right hk.le (abs_nonneg _))

-- Test section: a negative `x`. At `x = -1 / 4` and `a = 1 / 2` the first bound reads
-- `|log (3 / 4)| < log 2 / 2`, that is `log (4 / 3) < log 2 / 2`, or `(4 / 3) ^ 2 < 2`.
example : |Real.log (3 / 4)| < Real.log 2 / 2 := by
  have h := (abs_log_one_add_lt_and_abs_lt_exp_sub_one (1 / 2) (-(1 / 4)) (by norm_num)
    (by norm_num) (by rw [abs_neg, abs_of_pos (by norm_num)]; norm_num) (by norm_num)).1
  have hc : -Real.log (1 - 1 / 2) / (1 / 2) * |(-(1 / 4) : ℝ)| = Real.log 2 / 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    ring
  rwa [hc, show (1 : ℝ) + -(1 / 4) = 3 / 4 by norm_num] at h

-- Test section: the hypothesis `x ≠ 0` is needed. At `x = 0` both sides of each bound vanish, so
-- neither strict inequality holds, whatever `a` is.
example (a : ℝ) :
    ¬ |Real.log (1 + 0)| < -Real.log (1 - a) / a * |(0 : ℝ)| ∧
      ¬ |(0 : ℝ)| < a / (1 - Real.exp (-a)) * |Real.exp 0 - 1| := by
  simp

end MathlibExtTest.KPellLucasCloseToPowerOfTwo
