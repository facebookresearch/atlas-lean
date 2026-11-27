/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Polynomial.Coeff
import MathlibExt.NumberTheory.Recurrences.GFPLucasCatalan

namespace MetaMathlibExt

open Finset Polynomial

-- Clearing the power-of-two denominator includes the initial index.
example {α p₀ : ℤ} (hα : α * p₀ = 2) (p₁ g : ℤ[X]) :
    C α * generalizedFibonacciPolynomial (C p₀) p₁ (C α * p₁) g 0 = 2 := by
  simpa only [Nat.zero_div, zero_add, sum_range_one, mul_zero, Nat.choose_zero_right, Nat.cast_one,
    Nat.sub_zero, pow_zero, one_mul, mul_one] using gfp_lucas_catalan hα rfl g 0

-- When the discriminant vanishes, only the constant binomial term survives.
example (p : ℤ[X]) (n : ℕ) :
    generalizedFibonacciPolynomial 1 p (2 * p) (-(p ^ 2)) n = p ^ n := by
  have hd : 2 * p = C (2 : ℤ) * p := by simp
  have hD : 4 * -(p ^ 2) + (2 * p) ^ 2 = 0 := by ring
  have h := gfp_lucas_catalan (α := 2) (p₀ := 1) (by decide) hd (-(p ^ 2)) n
  rw [hD] at h
  simp [zero_pow_eq, mul_ite, mul_pow] at h
  have h₂ : (2 : ℤ[X]) ≠ 0 := by norm_num
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero n h₂) h₂)
  simpa only [mul_assoc, mul_left_comm] using h

end MetaMathlibExt
