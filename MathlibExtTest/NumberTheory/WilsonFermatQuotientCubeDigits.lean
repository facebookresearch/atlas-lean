/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WilsonFermatQuotientCubeDigits
import Mathlib.Tactic.NormNum

open Finset MathlibExt.NumberTheory.WilsonFaulhaberWanted

-- Compute the error directly from the factorial and the base-p digits.
private def digitError (p : ℕ) : ℚ :=
  let s := Icc 1 (p - 1)
  let d₀ (i : ℕ) : ℚ := ((i ^ (p - 1) - 1) / p % p : ℕ)
  let d₁ (i : ℕ) : ℚ := ((i ^ (p - 1) - 1) / p ^ 2 % p : ℕ)
  (Nat.factorial (p - 1) : ℚ) -
    (-1 + p * (∑ i ∈ s, d₀ i) + p ^ 2 * (∑ i ∈ s, (d₀ i + d₁ i)) -
      p ^ 2 / 2 * ((∑ i ∈ s, d₀ i) ^ 2 + ∑ i ∈ s, d₀ i ^ 2))

-- At the smallest odd prime the error is zero.
example : padicNorm 3 (digitError 3) ≤ (3 : ℚ) ^ (-3 : ℤ) := by
  have hs : Icc 1 (3 - 1) = ({1, 2} : Finset ℕ) := by decide
  have he : digitError 3 = 0 := by norm_num [digitError, hs, sum_insert, Nat.factorial_succ]
  rw [he, padicNorm.zero]
  norm_num

-- At p = 5 the third digit contributes and the error is divisible by 5³ but not by 5⁴.
example : padicNorm 5 (digitError 5) ≤ (5 : ℚ) ^ (-3 : ℤ) ∧
    ¬ padicNorm 5 (digitError 5) ≤ (5 : ℚ) ^ (-4 : ℤ) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hs : Icc 1 (5 - 1) = ({1, 2, 3, 4} : Finset ℕ) := by decide
  have he : digitError 5 = ((250 : ℤ) : ℚ) := by
    norm_num [digitError, hs, sum_insert, Nat.factorial_succ]
  rw [he]
  exact ⟨(padicNorm.dvd_iff_norm_le (n := 3)).mp (by decide),
    mt (padicNorm.dvd_iff_norm_le (n := 4)).mpr (by decide)⟩

-- The oddness hypothesis cannot be omitted.
example : ¬ padicNorm 2 (digitError 2) ≤ (2 : ℚ) ^ (-3 : ℤ) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hs : Icc 1 (2 - 1) = ({1} : Finset ℕ) := by decide
  have he : digitError 2 = ((2 : ℤ) : ℚ) := by
    norm_num [digitError, hs, Nat.factorial_succ]
  rw [he]
  exact mt (padicNorm.dvd_iff_norm_le (n := 3)).mpr (by decide)

example : padicNorm 5 (digitError 5) ≤ (5 : ℚ) ^ (-3 : ℤ) :=
  wilson_mod_prime_cube_digits 5 (by decide) (by decide)
