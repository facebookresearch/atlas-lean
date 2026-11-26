/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GibonacciPolynomialOddRatioSum

/-! # Specializations of the telescoping sum at odd multiples -/

namespace MetaMathlibExt.tsum_gibonacciPoly_pow_ratio_telescope

open Polynomial

local notation "F" => fun n : ℕ => aeval (3 / 2 : ℝ) (generalizedFibonacciPolynomial 0 1 X 1 n)
local notation "L" => fun n : ℕ => aeval (1 : ℝ) (generalizedFibonacciPolynomial 2 X X 1 n)

-- At x = 3/2 the first shifted Fibonacci ratio is 13/4 and its limit is 4.
example : ∑' n : ℕ, (F (2 * n + 1 + 2) ^ 2 / F (2 * n + 1) ^ 2 -
    F (2 * n + 3 + 2) ^ 2 / F (2 * n + 3) ^ 2) = -87 / 16 := by
  have h := tsum_gibonacciPoly_pow_ratio_telescope (x := 3 / 2) (by norm_num)
    (Or.inl rfl) (k := 1) (by decide) 2 2
  have hsqrt : √((3 / 2 : ℝ) ^ 2 + 4) = 5 / 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  simp only [Nat.mul_one] at h
  rw [h, hsqrt]
  norm_num [generalizedFibonacciPolynomial]

-- With zero shift, the cubed Lucas self-ratios give a zero sum.
example : ∑' n : ℕ, (L (2 * n + 1) ^ 3 / L (2 * n + 1) ^ 3 -
    L (2 * n + 3) ^ 3 / L (2 * n + 3) ^ 3) = 0 := by
  simpa [generalizedFibonacciPolynomial] using
    tsum_gibonacciPoly_pow_ratio_telescope (x := 1) zero_lt_one
      (Or.inr rfl) (k := 1) (by decide) 0 3

end MetaMathlibExt.tsum_gibonacciPoly_pow_ratio_telescope
