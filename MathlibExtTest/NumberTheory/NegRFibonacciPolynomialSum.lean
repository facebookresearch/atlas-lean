/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NegRFibonacciPolynomialSum
import Mathlib.Tactic.NormNum

/-! # Tests for the binomial sum indexed by the exponent of the inverse unit -/

open MetaMathlibExt

variable {A : Type*} [CommRing A] (x : A) (y : Aˣ)

example {r : ℕ} (hr : 2 ≤ r) : negRFibonacci r (0 : A) y 1 = 1 := by
  simpa using negRFibonacci_succ_eq_sum hr (0 : A) y 0

example : negRFibonacci 2 x y 2 = 0 := by
  rw [negRFibonacci_succ_eq_sum (r := 2) (by decide) x y 1]
  norm_num [Finset.sum_range_succ]

-- At n = 9 only k = 3, 4 contribute, both with odd powers of -x.
example :
    negRFibonacci 2 x y 10 = (↑y⁻¹ : A) ^ 3 * (-x) ^ 3 + 4 * (↑y⁻¹ : A) ^ 4 * (-x) := by
  rw [negRFibonacci_succ_eq_sum (r := 2) (by decide) x y 9]
  norm_num [Finset.sum_range_succ, Nat.choose]
