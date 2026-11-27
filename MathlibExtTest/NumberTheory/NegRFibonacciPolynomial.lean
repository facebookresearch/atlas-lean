/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NegRFibonacciPolynomial
import Mathlib.Tactic.NormNum

/-! # Tests for the binomial sum for negative-order Fibonacci polynomials -/

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
