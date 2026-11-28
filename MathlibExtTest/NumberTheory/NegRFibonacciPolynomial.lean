/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NegRFibonacciPolynomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for negative-order Fibonacci polynomials and their companion sequence -/

open MetaMathlibExt

variable {A : Type*} [CommRing A] (x : A) (y : Aˣ)

-- At n = 0 the empty path contributes one, even when x = 0.
example {r : ℕ} (hr : 2 ≤ r) : negRFibonacci r (0 : A) y 1 = 1 := by
  simpa using negRFibonacci_succ_eq_sum' hr (0 : A) y 0

-- At n = 1 the divisibility filter is empty.
example : negRFibonacci 2 x y 2 = 0 := by
  rw [negRFibonacci_succ_eq_sum' (r := 2) (by decide) x y 1]
  norm_num [Finset.sum_filter, Finset.sum_range_succ]

-- At n = 8 the filter admits k = 0, 2, 4, and the last binomial coefficient vanishes.
example : negRFibonacci 2 x y 9 = (↑y⁻¹ : A) ^ 4 + 3 * (↑y⁻¹ : A) ^ 3 * x ^ 2 := by
  rw [negRFibonacci_succ_eq_sum' (r := 2) (by decide) x y 8]
  norm_num [Finset.sum_filter, Finset.sum_range_succ, Nat.choose]

-- Order zero takes the zero branch at the first positive index.
example : negRLucas 0 (2 : ℤ) 1 1 = 0 := by decide +kernel

-- At order one the recurrence at index two uses both initial values.
example : negRLucas 1 x y 2 = (↑y⁻¹ : A) ^ 2 - 2 * ↑y⁻¹ * x := by
  rw [negRLucas_succ_of_le (r := 1) (n := 1) x y le_rfl le_rfl, Nat.sub_self,
    negRLucas_self x y le_rfl, negRLucas_zero]
  norm_num
  ring

-- At n = r the correction term is zero.
example {r : ℕ} (hr : 2 ≤ r) : negRLucas r x y r = (r : A) * ↑y⁻¹ := by
  rw [negRLucas_eq hr le_rfl, negRFibonacci_succ_of_le x y (by omega : 1 ≤ r) le_rfl]
  simp [negRFibonacci_zero, negRFibonacci_one]

-- At n = r + 1 the correction contributes one of the three copies of -x / y.
example : negRLucas 2 x y 3 = -(3 * x * ↑y⁻¹) := by
  rw [negRLucas_eq (r := 2) (n := 3) (by decide) (by decide),
    negRFibonacci_succ_of_le (r := 2) (n := 3) x y (by decide) (by decide),
    negRFibonacci_succ_of_lt (r := 2) (n := 1) x y (by decide) (by decide)]
  simp [negRFibonacci_one]
  ring

-- The formula applies without any invertibility assumption on x, including x = 0.
example : negRLucas 2 (0 : A) y 4 = 2 * (↑y⁻¹ : A) ^ 2 := by
  rw [negRLucas_eq (r := 2) (n := 4) (by decide) (by decide),
    negRFibonacci_succ_of_le (r := 2) (n := 4) (0 : A) y (by decide) (by decide),
    negRFibonacci_succ_of_le (r := 2) (n := 2) (0 : A) y (by decide) (by decide)]
  simp [negRFibonacci_one, pow_two]
