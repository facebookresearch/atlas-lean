/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GibonacciPolynomialSquareSumsRevisited

/-! # Fibonacci and Lucas specializations of the shifted square sum -/

namespace MathlibExtTest.NumberTheory.GibonacciPolynomialSquareSumsRevisited

open MetaMathlibExt Polynomial

local notation "F" => fun n : ℕ => aeval (1 : ℝ) (generalizedFibonacciPolynomial 0 1 X 1 n)
local notation "L" => fun n : ℕ => aeval (1 : ℝ) (generalizedFibonacciPolynomial 2 X X 1 n)

-- The Fibonacci case at `x = 1` with `k = r = 1` has unit numerators.
example : ∑' n : ℕ, (1 : ℝ) / (F (2 * (n + 1) + 1) ^ 2 - 1) = (3 - √5) / 2 := by
  have h := tsum_fib_mul_div_gibonacciPoly_shift_sq_add (x := 1) zero_lt_one
    (Or.inl ⟨rfl, rfl, rfl⟩) (k := 1) (by decide) 1
  norm_num [generalizedFibonacciPolynomial, sub_eq_add_neg, add_comm] at h ⊢
  rw [h]
  ring

-- The Lucas case at `x = 1` with `k = 2` and `r = 1` starts at `15/116`.
example : ∑' n : ℕ, (15 : ℝ) / (L (2 * (n + 1) * 2 + 1) ^ 2 - 5) = 3 / 4 - (√5 - 1) / 2 := by
  have h := tsum_fib_mul_div_gibonacciPoly_shift_sq_add (x := 1) zero_lt_one
    (Or.inr ⟨rfl, rfl, rfl⟩) (k := 2) (by decide) 1
  norm_num [generalizedFibonacciPolynomial, map_ofNat, sub_eq_add_neg, add_comm] at h ⊢
  rw [h]
  ring

end MathlibExtTest.NumberTheory.GibonacciPolynomialSquareSumsRevisited
