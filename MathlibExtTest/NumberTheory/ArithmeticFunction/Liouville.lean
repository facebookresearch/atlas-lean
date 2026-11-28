/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Tests for the Liouville function
-/

@[expose] public section

open ArithmeticFunction

/-! ### Concrete and boundary values -/

example : liouville 12 = -1 := by decide +kernel
example : liouville 36 = 1 := by decide +kernel
example : liouville 0 = 0 := by simp
example : liouville 1 = 1 := liouville_apply_one
example : liouville (2 ^ 5) = -1 := by rw [liouville_apply_prime_pow Nat.prime_two]; norm_num
example (p : ℕ) (hp : p.Prime) : liouville (p ^ 0) = 1 := by
  rw [liouville_apply_prime_pow hp]; norm_num
example : |liouville 30| = 1 := abs_liouville (by norm_num)
example : |liouville 0| ≤ 1 := abs_liouville_le_one 0

/-! ### The divisor sum of `λ` is the indicator of the squares -/

example : ∑ d ∈ (36 : ℕ).divisors, liouville d = 1 := by
  rw [sum_divisors_liouville (by norm_num), ite_eq_left ⟨6, rfl⟩]
example : ∑ d ∈ (12 : ℕ).divisors, liouville d = 0 := by
  rw [sum_divisors_liouville (by norm_num), ite_eq_right (by decide +kernel)]
-- Direct evaluation agrees.
example : ∑ d ∈ (12 : ℕ).divisors, liouville d = 0 := by decide +kernel

/-! ### Dirichlet series -/

example : LSeriesSummable (fun n ↦ (liouville n : ℂ)) 2 :=
  LSeriesSummable_liouville (by norm_num)

-- `∑ λ(n) / n² = ζ(4) / ζ(2) = π² / 15`.
example : LSeries (fun n ↦ (liouville n : ℂ)) 2 = (Real.pi : ℂ) ^ 2 / 15 := by
  rw [LSeries_liouville_eq_riemannZeta_two_mul_div (by norm_num),
    show (2 : ℂ) * 2 = 4 by norm_num, riemannZeta_four, riemannZeta_two]
  have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

-- The square-indicator series converges up to `re s > 1/2`.
example : LSeries (fun n ↦ if IsSquare n then 1 else 0) 1 = riemannZeta 2 := by
  simpa using LSeries_isSquare_indicator (s := 1) (by norm_num)
