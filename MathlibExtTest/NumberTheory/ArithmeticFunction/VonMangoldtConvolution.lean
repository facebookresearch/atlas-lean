/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.VonMangoldtConvolution

/-!
# Tests for the Dirichlet square of the von Mangoldt function
-/

@[expose] public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

example : ∑ d ∈ (1 : ℕ).divisors, (μ d : ℚ) = 1 := by
  rw [sum_divisors_moebius]; simp
example : ∑ d ∈ (12 : ℕ).divisors, (μ d : ℚ) = 0 := by
  rw [sum_divisors_moebius]; simp
-- Boundary `n = 0`: the empty divisor sum.
example : ∑ d ∈ (0 : ℕ).divisors, (μ d : ℚ) = 0 := by
  rw [sum_divisors_moebius]; simp

-- `(Λ * Λ)(1) = 0`.
example : (Λ * Λ) 1 = 0 := by
  rw [vonMangoldt_mul_vonMangoldt_apply]; simp

-- `(Λ * Λ)(p) = 0` at a prime `p` (the factorisations `1 · p` and `p · 1` both contain `Λ 1 = 0`),
-- recovered from the identity as `log² p - log² p`.
example {p : ℕ} (hp : p.Prime) : (Λ * Λ) p = 0 := by
  rw [vonMangoldt_mul_vonMangoldt_apply, Nat.Prime.sum_divisors hp, vonMangoldt_apply_prime hp,
    moebius_apply_prime hp]
  simp
  ring

-- `(Λ * Λ)(p²) = log² p`, from the identity: `2 log² p + (-log² p)`.
example {p : ℕ} (hp : p.Prime) : (Λ * Λ) (p ^ 2) = Real.log p ^ 2 := by
  rw [vonMangoldt_mul_vonMangoldt_apply, vonMangoldt_apply_pow two_ne_zero,
    vonMangoldt_apply_prime hp, Nat.divisors_prime_pow hp, sum_map, sum_range_succ,
    sum_range_succ, sum_range_one]
  simp [moebius_apply_prime hp, moebius_apply_prime_pow hp, Real.log_pow]
  ring

example (x : ℝ) (hx : x ≠ 0) :
    ∑ d ∈ (1 : ℕ).divisors, (μ d : ℝ) * Real.log (x / d) ^ 2 = Real.log x ^ 2 := by
  rw [sum_divisors_moebius_mul_log_div_sq hx]; simp
