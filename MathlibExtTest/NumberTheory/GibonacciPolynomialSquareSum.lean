/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GibonacciPolynomialSquareSum

/-! # Fibonacci and Lucas specializations at one -/

namespace MetaMathlibExt.GibonacciPolynomialSquareSum

open Polynomial

local notation "F" => fun n : ℕ => aeval (1 : ℝ) (generalizedFibonacciPolynomial 0 1 X 1 n)
local notation "L" => fun n : ℕ => aeval (1 : ℝ) (generalizedFibonacciPolynomial 2 X X 1 n)

-- The odd-step Fibonacci case detects the sign of the numerator.
example : ∑' n : ℕ, (-1 : ℝ) / (F (2 * (n + 1)) ^ 2 + 1) = (1 - √5) / 2 := by
  have h := tsum_fib_mul_div_gibonacciPoly_sq_add (x := 1) zero_lt_one
    (Or.inl ⟨rfl, rfl, rfl⟩) (k := 1) (by decide) 1
  norm_num [generalizedFibonacciPolynomial] at h
  rw [h]
  ring

-- For the even-step Lucas case the denominator contains the discriminant five.
example : ∑' n : ℕ, (-15 : ℝ) / (L (2 * (n + 1) * 2) ^ 2 + 5) =
    4 / 3 - (1 + √5) / 2 := by
  have h := tsum_fib_mul_div_gibonacciPoly_sq_add (x := 1) zero_lt_one
    (Or.inr ⟨rfl, rfl, rfl⟩) (k := 2) (by decide) 1
  norm_num [generalizedFibonacciPolynomial, map_ofNat] at h
  exact h

end MetaMathlibExt.GibonacciPolynomialSquareSum
