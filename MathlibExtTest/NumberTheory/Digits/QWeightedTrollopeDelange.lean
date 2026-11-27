/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.QWeightedTrollopeDelange

/-! # Tests for the `q`-weighted Trollope–Delange formula and dyadic fluctuation -/

namespace MetaMathlibExt.qWeightedDigitPartialSum_dyadic_fluctuation

open Finset

-- The definition reads the binary digits least significant first: `6 = 110₂`.
example (q : ℤ) : qWeightedDigitSum q 6 = q ^ 2 + q ^ 3 := by
  simp [qWeightedDigitSum, sum_range_succ]

-- The binary recursion computes the same values: `11 = 1011₂`.
example (q : ℤ) : qWeightedDigitSum q 11 = q + q ^ 2 + q ^ 4 := by
  simp [qWeightedDigitSum_of_pos, qWeightedDigitSum_zero]
  ring

-- For `q = 1` the weighted digit sum is the number of ones: `7 = 111₂`.
example : qWeightedDigitSum (1 : ℤ) 7 = 3 := by
  simp [qWeightedDigitSum_of_pos, qWeightedDigitSum_zero]

-- `S_q(4) = s_q(0) + s_q(1) + s_q(2) + s_q(3) = 2q + 2q²`.
example (q : ℤ) : qWeightedDigitPartialSum q 4 = 2 * q + 2 * q ^ 2 := by
  simp [qWeightedDigitPartialSum, sum_range_succ, qWeightedDigitSum_of_pos,
    qWeightedDigitSum_zero]
  ring

-- The hypotheses are satisfiable: `q = 1` (the classical Takagi case `a = 1/2`), `N = 3`, `j = 4`.
example : (qWeightedDigitPartialSum (1 : ℂ) (2 * 4) -
      ((4 : ℕ) / 2 ^ (3 - 1) : ℂ) * qWeightedDigitPartialSum (1 : ℂ) (2 ^ 3)) / (2 * 1) ^ (3 - 1) =
    -1 * takagiLandsberg (1 / (2 * 1) : ℂ) ((4 : ℕ) / 2 ^ (3 - 1) : ℝ) :=
  qWeightedDigitPartialSum_dyadic_fluctuation 1 (by norm_num) 3 (by norm_num) 4 (by norm_num)

-- At the right endpoint `t = 1` the fluctuation vanishes, so `𝒯_a(1) = 0`.
example (q : ℂ) (hq : 1 / 2 < ‖q‖) (N : ℕ) (hN : 0 < N) :
    takagiLandsberg (1 / (2 * q)) 1 = 0 := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    norm_num at hq
  have h := qWeightedDigitPartialSum_dyadic_fluctuation q hq N hN (2 ^ (N - 1)) le_rfl
  rw [show 2 * 2 ^ (N - 1) = 2 ^ N by rw [← pow_succ', Nat.sub_add_cancel hN]] at h
  push_cast at h
  rw [div_self (pow_ne_zero _ two_ne_zero), div_self (pow_ne_zero _ two_ne_zero), one_mul,
    sub_self, zero_div] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (neg_ne_zero.mpr hq0)

-- At `N = 2`, `j = 1` the theorem determines `𝒯_a(1/2) = τ(1/2) = 1/2`.
example (q : ℂ) (hq : 1 / 2 < ‖q‖) : takagiLandsberg (1 / (2 * q)) (1 / 2) = 1 / 2 := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    norm_num at hq
  have h := qWeightedDigitPartialSum_dyadic_fluctuation q hq 2 (by norm_num) 1 (by norm_num)
  have hS2 : qWeightedDigitPartialSum q (2 * 1) = q := by
    simp [qWeightedDigitPartialSum, sum_range_succ, qWeightedDigitSum_of_pos,
      qWeightedDigitSum_zero]
  have hS4 : qWeightedDigitPartialSum q (2 ^ 2) = 2 * q + 2 * q ^ 2 := by
    simp [qWeightedDigitPartialSum, sum_range_succ, qWeightedDigitSum_of_pos,
      qWeightedDigitSum_zero]
    ring
  rw [show ((1 : ℕ) : ℝ) / 2 ^ (2 - 1) = 1 / 2 by norm_num,
    show ((1 : ℕ) : ℂ) / 2 ^ (2 - 1) = 1 / 2 by norm_num,
    show (2 * q) ^ (2 - 1) = 2 * q by norm_num, hS2, hS4,
    div_eq_iff (mul_ne_zero two_ne_zero hq0)] at h
  generalize takagiLandsberg (1 / (2 * q)) (1 / 2) = T at h ⊢
  have h' : q ^ 2 * (2 * T - 1) = 0 := by linear_combination h
  linear_combination (mul_eq_zero.mp h').resolve_left (pow_ne_zero 2 hq0) / 2

-- At `N = 3`, `j = 1` it gives `𝒯_a(1/4) = τ(1/4) + a τ(1/2) = 1/4 + 1/(4q)`.
example (q : ℂ) (hq : 1 / 2 < ‖q‖) :
    takagiLandsberg (1 / (2 * q)) (1 / 4) = 1 / 4 + 1 / (4 * q) := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    norm_num at hq
  have h := qWeightedDigitPartialSum_dyadic_fluctuation q hq 3 (by norm_num) 1 (by norm_num)
  have hS2 : qWeightedDigitPartialSum q (2 * 1) = q := by
    simp [qWeightedDigitPartialSum, sum_range_succ, qWeightedDigitSum_of_pos,
      qWeightedDigitSum_zero]
  have hS8 : qWeightedDigitPartialSum q (2 ^ 3) = 4 * (q + q ^ 2 + q ^ 3) := by
    simp [qWeightedDigitPartialSum, sum_range_succ, qWeightedDigitSum_of_pos,
      qWeightedDigitSum_zero]
    ring
  rw [show ((1 : ℕ) : ℝ) / 2 ^ (3 - 1) = 1 / 4 by norm_num,
    show ((1 : ℕ) : ℂ) / 2 ^ (3 - 1) = 1 / 4 by norm_num,
    show (2 * q) ^ (3 - 1) = (2 * q) ^ 2 by norm_num, hS2, hS8,
    div_eq_iff (pow_ne_zero 2 (mul_ne_zero two_ne_zero hq0))] at h
  generalize takagiLandsberg (1 / (2 * q)) (1 / 4) = T at h ⊢
  have h' : q ^ 2 * (4 * q * T - 1 - q) = 0 := by linear_combination h
  have h4 : T * (4 * q) = 1 + q := by
    linear_combination (mul_eq_zero.mp h').resolve_left (pow_ne_zero 2 hq0)
  rw [eq_div_of_mul_eq (mul_ne_zero (by norm_num) hq0) h4]
  field_simp
  ring

end MetaMathlibExt.qWeightedDigitPartialSum_dyadic_fluctuation

namespace MetaMathlibExt.qWeighted_trollopeDelange

open Finset

-- At `n = 1`, the fractional logarithm is zero and the formula gives `𝒯_{1/4}(1/2) = 1/2`.
example : takagiLandsberg (1 / 4 : ℝ) (1 / 2) = 1 / 2 := by
  have h := qWeighted_trollopeDelange (q := 2) (hq := by norm_num) (hq1 := by norm_num)
    (n := 1) (hn := by decide)
  norm_num [qWeightedDigitPartialSum, qWeightedDigitSum_zero, Real.logb_one, Real.rpow_neg_one,
    one_div] at h ⊢
  linarith

-- For `q = -1` and `n = 3`, the partial sum and the geometric term both cancel.
example : takagiLandsberg (-1 / 2 : ℝ) (3 / 4) = 0 := by
  have h := qWeighted_trollopeDelange (-1) (by norm_num) (by norm_num) 3 (by decide)
  have hS : qWeightedDigitPartialSum (-1 : ℝ) 3 = 0 := by
    norm_num [qWeightedDigitPartialSum, sum_range_succ, qWeightedDigitSum_of_pos,
      qWeightedDigitSum_zero]
  have hlog : Nat.log 2 3 = 1 := by decide
  have hfloor : ⌊Real.logb 2 (3 : ℕ)⌋ = 1 := by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · rw [Int.cast_one, Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
      norm_num
    · rw [Int.cast_one, Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
      norm_num
  have harg : (2 : ℝ) ^ (-(1 - Int.fract (Real.logb 2 (3 : ℕ)))) = 3 / 4 := by
    rw [Int.fract, hfloor, Int.cast_one, show ∀ x : ℝ, -(1 - (x - 1)) = x - 2 by
      intro x
      ring]
    rw [Real.rpow_sub (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have hscale := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
    (1 - Int.fract (Real.logb 2 (3 : ℕ)))
  rw [hS, hlog, harg] at h
  norm_num at h ⊢
  exact h.resolve_left hscale.ne'

end MetaMathlibExt.qWeighted_trollopeDelange
