/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NegRFibonacciGeneratingFunction

/-! # Tests for the generating function of the negative-order Fibonacci polynomials -/

open MetaMathlibExt PowerSeries

variable {A : Type*} [CommRing A] {r : ℕ} (hr : 2 ≤ r) (x : A) (y : Aˣ)

-- At x = 0 and y = 1, only the shift by r remains.
example : (1 - X ^ r) * mk (fun n => negRFibonacci r (0 : A) 1 (n + 1)) = 1 := by
  simpa using negRFibonacci_generatingFunction hr (0 : A) 1

-- The coefficient at degree r + 1 detects the sign of the first term involving x.
example : negRFibonacci r x y (r + 2) = -(x * ↑y⁻¹) := by
  have h := congrArg (coeff (r + 1) (R := A)) (negRFibonacci_generatingFunction hr x y)
  have h₂ : negRFibonacci r x y 2 = 0 := negRFibonacci_succ_of_lt x y (le_refl 1) (by omega)
  simpa [add_mul, sub_mul, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_one, h₂,
    negRFibonacci_one, add_eq_zero_iff_eq_neg] using h
