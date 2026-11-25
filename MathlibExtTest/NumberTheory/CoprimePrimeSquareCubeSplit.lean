/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CoprimePrimeSquareCubeSplit
import Mathlib.Tactic.NormNum

/-! # Tests for splitting a prime square times a cube into coprime factors -/

open MetaMathlibExt

-- The square goes on the left, even when the prime also divides the cube root.
example : ∃ x y : ℤ, x < 0 ∧ -32 = 4 * x ^ 3 ∧ 27 = y ^ 3 := by
  obtain ⟨x, y, h⟩ := cube_split_of_mul_eq_prime_sq_mul_cube_of_gcd_eq_one
    (p := 2) (R := -32) (S := 27) (C := -6) (by decide) (by decide) (by decide)
  norm_num at h
  have hsplit : (-32 : ℤ) = 4 * x ^ 3 ∧ (27 : ℤ) = y ^ 3 := by omega
  refine ⟨x, y, ?_, hsplit⟩
  by_contra! hnonneg
  have := pow_nonneg hnonneg 3
  omega

-- The square goes on the right; the factor that is a cube can be negative too.
example : ∃ x y : ℤ, x < 0 ∧ -27 = x ^ 3 ∧ 32 = 4 * y ^ 3 := by
  obtain ⟨x, y, h⟩ := cube_split_of_mul_eq_prime_sq_mul_cube_of_gcd_eq_one
    (p := 2) (R := -27) (S := 32) (C := -6) (by decide) (by decide) (by decide)
  norm_num at h
  have hsplit : (-27 : ℤ) = x ^ 3 ∧ (32 : ℤ) = 4 * y ^ 3 := by omega
  refine ⟨x, y, ?_, hsplit⟩
  by_contra! hnonneg
  have := pow_nonneg hnonneg 3
  omega

-- With a zero product, the square goes on the zero factor, not the signed unit.
example : ∃ x y : ℤ, 0 = 4 * x ^ 3 ∧ -1 = y ^ 3 := by
  obtain ⟨x, y, h⟩ := cube_split_of_mul_eq_prime_sq_mul_cube_of_gcd_eq_one
    (p := 2) (R := 0) (S := -1) (C := 0) (by decide) (by decide) (by decide)
  have hp : ((2 : ℕ) : ℤ) ^ 2 = 4 := by norm_num
  rw [hp] at h
  exact ⟨x, y, by omega⟩

example : ∃ x y : ℤ, 1 = x ^ 3 ∧ 0 = 4 * y ^ 3 := by
  obtain ⟨x, y, h⟩ := cube_split_of_mul_eq_prime_sq_mul_cube_of_gcd_eq_one
    (p := 2) (R := 1) (S := 0) (C := 0) (by decide) (by decide) (by decide)
  have hp : ((2 : ℕ) : ℤ) ^ 2 = 4 := by norm_num
  rw [hp] at h
  exact ⟨x, y, by omega⟩
