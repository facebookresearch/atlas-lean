/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RLucasPolynomialAlternatingSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for alternating sums of the r-Lucas polynomials -/

open MetaMathlibExt

-- At n = r - 1 the final window reaches V₀ = s + 1: for r = 3, s = 4, x = 2 and y = 1 the
-- alternating sum -V₁ + V₂ = -2 + 4 is 2.
example : ∑ j ∈ Finset.Icc 1 2, (-1) ^ j * rLucasPolynomial 3 4 (2 : ℚ) 1 j = 2 := by
  rw [sum_neg_one_pow_mul_rLucasPolynomial (by decide) (by decide) _ _ _ (by norm_num)]
  have h (i : ℕ) (hi : i < 3) :
      rLucasPolynomial 3 4 (2 : ℚ) 1 (i + 1) = 2 ^ (i + 1) :=
    rLucasPolynomial_succ_of_lt _ _ _ hi
  norm_num [show Finset.Icc 1 3 = {1, 2, 3} by decide, rLucasPolynomial_zero,
    h 0 (by decide), h 1 (by decide), h 2 (by decide)]

-- For the Lucas numbers (r = 1, s = 1, x = y = 1) the alternating sum -L₁ + L₂ - ... of the
-- first k + 1 terms from index one is 1 + (-1)^(k+1) L_k.
example (k : ℕ) :
    ∑ j ∈ Finset.Icc 1 (k + 1), (-1) ^ j * rLucasPolynomial 1 1 (1 : ℚ) 1 j =
      1 + (-1) ^ (k + 1) * rLucasPolynomial 1 1 (1 : ℚ) 1 k := by
  rw [sum_neg_one_pow_mul_rLucasPolynomial le_rfl (by omega) _ _ _ (by norm_num),
    rLucasPolynomial_succ_of_le (n := k + 1) 1 1 1 (by omega)]
  simp
  ring

-- The identity also covers n = 0, which forces r = 1: the sum is empty, so the quotient is 1.
example (s : ℕ) (x y : ℚ) (hP : 1 + x + (-1) ^ 1 * y ≠ 0) :
    (1 - (-1) ^ 1 * s * y + (-1) ^ 0 * rLucasPolynomial 1 s x y (0 + 1)
        + (-1) ^ 1 * y * ∑ j ∈ Finset.Icc 1 1,
            (-1) ^ (0 + j - 1) * rLucasPolynomial 1 s x y (0 + j - 1))
      / (1 + x + (-1) ^ 1 * y) = 1 := by
  have h := sum_neg_one_pow_mul_rLucasPolynomial (n := 0) le_rfl le_rfl s x y hP
  rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty] at h
  linear_combination -h

-- Without `1 + x + (-1)^r y ≠ 0` the identity fails: for r = 1, s = 0, x = 0, y = 1 and n = 1
-- the right side divides by zero, so it is -1, while the left side is -V₁ = 0.
example :
    ∑ j ∈ Finset.Icc 1 1, (-1) ^ j * rLucasPolynomial 1 0 (0 : ℚ) 1 j ≠
      (1 - (-1) ^ 1 * ((0 : ℕ) : ℚ) * 1 + (-1) ^ 1 * rLucasPolynomial 1 0 (0 : ℚ) 1 (1 + 1)
          + (-1) ^ 1 * 1 * ∑ j ∈ Finset.Icc 1 1,
              (-1) ^ (1 + j - 1) * rLucasPolynomial 1 0 (0 : ℚ) 1 (1 + j - 1))
        / (1 + 0 + (-1) ^ 1 * 1) - 1 := by
  norm_num [rLucasPolynomial_succ_of_lt (n := 0) 0 (0 : ℚ) 1 (by decide : 0 < 1)]

-- Without `r ≤ n + 1` the identity fails: for r = 3, n = 0, s = 0, x = 0 and y = -1 the truncated
-- indices 0 + j - 3 all become 0, so the right side is (1 + 3 V₀) / 2 - 1 = 1, not 0.
example :
    ∑ j ∈ Finset.Icc 1 0, (-1) ^ j * rLucasPolynomial 3 0 (0 : ℚ) (-1) j ≠
      (1 - (-1) ^ 3 * ((0 : ℕ) : ℚ) * (-1) + (-1) ^ 0 * rLucasPolynomial 3 0 (0 : ℚ) (-1) (0 + 1)
          + (-1) ^ 3 * (-1) * ∑ j ∈ Finset.Icc 1 3,
              (-1) ^ (0 + j - 3) * rLucasPolynomial 3 0 (0 : ℚ) (-1) (0 + j - 3))
        / (1 + 0 + (-1) ^ 3 * (-1)) - 1 := by
  have h0 (j : ℕ) (hj : j ∈ Finset.Icc 1 3) :
      (-1) ^ (0 + j - 3) * rLucasPolynomial 3 0 (0 : ℚ) (-1) (0 + j - 3) = 1 := by
    rw [Nat.sub_eq_zero_of_le (by have := (Finset.mem_Icc.mp hj).2; omega),
      rLucasPolynomial_zero]
    norm_num
  rw [Finset.sum_congr rfl h0,
    rLucasPolynomial_succ_of_lt (n := 0) 0 (0 : ℚ) (-1) (by decide : 0 < 3)]
  norm_num
