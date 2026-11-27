/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RFibonacciPolynomialSum
import Mathlib.Tactic.NormNum

/-! # Tests for the partial sums of the r-Fibonacci polynomials -/

open MetaMathlibExt

-- With r = 2 the recurrence U_(n+1) = x U_n + y U_(n-2) gives 0, 1, x, x², x³ + y, x⁴ + 2xy.
example (x y : ℤ) : rFibonacciPolynomial 2 x y 5 = x ^ 4 + 2 * x * y := by
  have h (i : ℕ) (hi : i < 2) : rFibonacciPolynomial 2 x y (i + 1) = x ^ i :=
    rFibonacciPolynomial_succ_of_lt x y hi
  have hs (n : ℕ) (hn : 2 ≤ n) : rFibonacciPolynomial 2 x y (n + 1) =
      x * rFibonacciPolynomial 2 x y n + y * rFibonacciPolynomial 2 x y (n - 2) :=
    rFibonacciPolynomial_succ_of_le x y hn
  rw [hs 4 (by decide), hs 3 (by decide), hs 2 (by decide), h 1 (by decide), h 0 (by decide),
    rFibonacciPolynomial_zero]
  ring

-- For the Fibonacci numbers (r = 1, x = y = 1) the first n terms sum to F_(n+2) - 1.
example (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, rFibonacciPolynomial 1 (1 : ℚ) 1 j =
      rFibonacciPolynomial 1 (1 : ℚ) 1 (n + 2) - 1 := by
  rw [sum_rFibonacciPolynomial le_rfl _ _ (by norm_num),
    rFibonacciPolynomial_succ_of_le (n := n + 1) 1 1 (by omega)]
  simp
  ring

-- For n < r the window of the last r indices reaches index 0, whose term is zero: with r = 3 and
-- n = 2 the closed form returns U₁ + U₂ = 1 + x.
example (x y : ℚ) (hP : 1 - x - y ≠ 0) :
    ∑ j ∈ Finset.Icc 1 2, rFibonacciPolynomial 3 x y j = 1 + x := by
  rw [sum_rFibonacciPolynomial (by decide) x y hP]
  have h (i : ℕ) (hi : i < 3) : rFibonacciPolynomial 3 x y (i + 1) = x ^ i :=
    rFibonacciPolynomial_succ_of_lt _ _ hi
  rw [div_eq_iff hP]
  norm_num [show Finset.Icc 1 3 = {1, 2, 3} by decide, rFibonacciPolynomial_zero,
    h 0 (by decide), h 1 (by decide), h 2 (by decide)]
  ring

-- Without `1 - x - y ≠ 0` the identity fails: for r = 1, x = 1, y = 0 and n = 1 the right side
-- divides by zero, so it is 0, while the left side is U₁ = 1.
example :
    ∑ j ∈ Finset.Icc 1 1, rFibonacciPolynomial 1 (1 : ℚ) 0 j ≠
      (1 - rFibonacciPolynomial 1 (1 : ℚ) 0 (1 + 1)
          - 0 * ∑ j ∈ Finset.Icc 1 1, rFibonacciPolynomial 1 (1 : ℚ) 0 (1 + j - 1))
        / (1 - 1 - 0) := by
  norm_num [rFibonacciPolynomial_succ_of_lt (n := 0) (1 : ℚ) 0 (by decide : 0 < 1)]

-- Without `1 ≤ r` the identity fails: for r = 0 every term vanishes, while the right side at
-- n = 0 is 1 / (1 - x - y).
example :
    ∑ j ∈ Finset.Icc 1 0, rFibonacciPolynomial 0 (0 : ℚ) 0 j ≠
      (1 - rFibonacciPolynomial 0 (0 : ℚ) 0 (0 + 1)
          - 0 * ∑ j ∈ Finset.Icc 1 0, rFibonacciPolynomial 0 (0 : ℚ) 0 (0 + j - 0))
        / (1 - 0 - 0) := by
  norm_num [rFibonacciPolynomial_succ_of_le (r := 0) (n := 0) (0 : ℚ) 0 le_rfl,
    rFibonacciPolynomial_zero]
