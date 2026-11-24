/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeGCDCubeSplit
import Mathlib.Tactic.NormNum

/-! # Tests for splitting a prime square times a cube -/

open MetaMathlibExt

-- When both primes are two, both reduced factors can be units of opposite signs.
example : ∃ x y : ℤ, -2 = 2 * x ^ 3 ∧ 2 = 2 * y ^ 3 := by
  obtain ⟨x, y, h⟩ := cube_split_of_mul_eq_prime_sq_mul_cube_of_gcd_prime
    (p := 2) (R := -2) (S := 2) (C := -1) (by decide) (by decide) (by decide)
  norm_num [Int.gcd_def] at h
  exact ⟨x, y, by omega⟩

-- The extra gcd and the prime square can occur in opposite factors.
example : ∃ x y : ℤ, -18 = 18 * x ^ 3 ∧ 4 = 4 * y ^ 3 := by
  obtain ⟨x, y, h⟩ := cube_split_of_mul_eq_prime_sq_mul_cube_of_gcd_prime
    (p := 3) (R := -18) (S := 4) (C := -2) (by decide) (by decide) (by decide)
  norm_num [Int.gcd_def] at h
  have hodd : Odd (3 : ℕ) := by decide
  have hgap : y ^ 3 ≤ 1 ^ 3 ∨ 2 ^ 3 ≤ y ^ 3 :=
    (show y ≤ 1 ∨ 2 ≤ y by omega).imp hodd.pow_le_pow.mpr hodd.pow_le_pow.mpr
  exact ⟨x, y, by omega⟩

-- A vanishing product still admits a cube for the nonzero factor divided by its gcd.
example : ∃ z : ℤ, -5 = 5 * z ^ 3 := by
  obtain ⟨x, y, h⟩ := cube_split_of_mul_eq_prime_sq_mul_cube_of_gcd_prime
    (p := 2) (R := 0) (S := -5) (C := 0) (by decide) (by decide) (by decide)
  norm_num [Int.gcd_def] at h
  have hz : -5 = 5 * x ^ 3 ∨ -5 = 5 * y ^ 3 := by omega
  exact hz.elim (fun hx => ⟨x, hx⟩) (fun hy => ⟨y, hy⟩)
