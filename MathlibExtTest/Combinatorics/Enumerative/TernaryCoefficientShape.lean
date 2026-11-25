/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TernaryCoefficientShape
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

open Polynomial MetaMathlibExt

private def Dense (c d : ℕ) : Prop :=
  ∀ k ≤ c + d, ¬ (3 : ℤ) ∣ ((X - 1) ^ c * (X + 1) ^ d : ℤ[X]).coeff k

example : Dense 0 0 := by
  intro k hk
  have : k = 0 := by omega
  subst k
  norm_num

example : Dense 1 0 := by
  intro k hk
  interval_cases k <;> norm_num [coeff_sub, coeff_X, coeff_one]

-- A quadratic residual passes a nonconstant quotient down the induction.
example : let c := 2; let d := 3; ∃ i j : ℕ, j < i ∧
    (c + d + 1 = 3 ^ j ∨ c + d + 1 = 2 * 3 ^ j ∨
      c + d + 1 = 3 ^ i + 3 ^ j ∨ c + d + 1 = 2 * 3 ^ i + 3 ^ j) := by
  dsimp
  apply coeff_not_dvd_three_shape 2 3
  intro k hk
  have hp : ((X - 1) ^ 2 * (X + 1) ^ 3 : ℤ[X]) =
      monomial 0 1 + monomial 1 1 + monomial 2 (-2) +
        monomial 3 (-2) + monomial 4 1 + monomial 5 1 := by
    simp only [← C_mul_X_pow_eq_monomial, map_ofNat, map_neg, C_1]
    ring
  rw [hp]
  interval_cases k <;> norm_num [coeff_add, coeff_one, coeff_monomial, Finsupp.single_apply]

-- The `(1, 2)` residual has an alternating quotient.
example : let c := 4; let d := 2; ∃ i j : ℕ, j < i ∧
    (c + d + 1 = 3 ^ j ∨ c + d + 1 = 2 * 3 ^ j ∨
      c + d + 1 = 3 ^ i + 3 ^ j ∨ c + d + 1 = 2 * 3 ^ i + 3 ^ j) := by
  dsimp
  apply coeff_not_dvd_three_shape 4 2
  intro k hk
  have hp : ((X - 1) ^ 4 * (X + 1) ^ 2 : ℤ[X]) =
      monomial 0 1 + monomial 1 (-2) + monomial 2 (-1) +
        monomial 3 4 + monomial 4 (-1) + monomial 5 (-2) +
        monomial 6 1 := by
    simp only [← C_mul_X_pow_eq_monomial, map_ofNat, map_neg, C_1]
    ring
  rw [hp]
  interval_cases k <;> norm_num [coeff_add, coeff_one, coeff_monomial, Finsupp.single_apply]

-- The `(2, 1)` residual has a constant coefficient sequence in its quotient.
-- The telescoping binomial has degree 3, so its proof descends once more.
example : let c := 8; let d := 1; ∃ i j : ℕ, j < i ∧
    (c + d + 1 = 3 ^ j ∨ c + d + 1 = 2 * 3 ^ j ∨
      c + d + 1 = 3 ^ i + 3 ^ j ∨ c + d + 1 = 2 * 3 ^ i + 3 ^ j) := by
  dsimp
  apply coeff_not_dvd_three_shape 8 1
  intro k hk
  have hp : ((X - 1) ^ 8 * (X + 1) ^ 1 : ℤ[X]) =
      monomial 0 1 + monomial 1 (-7) + monomial 2 20 +
        monomial 3 (-28) + monomial 4 14 + monomial 5 14 +
        monomial 6 (-28) + monomial 7 20 + monomial 8 (-7) +
        monomial 9 1 := by
    simp only [← C_mul_X_pow_eq_monomial, map_ofNat, map_neg, C_1]
    ring
  rw [hp]
  interval_cases k <;> norm_num [coeff_add, coeff_one, coeff_monomial, Finsupp.single_apply]

-- Equal low digits can make the hypothesis fail even at degree 1.
example : ¬ Dense 1 1 := by
  intro h
  apply h 1 (by decide)
  have hp : ((X - 1) ^ 1 * (X + 1) ^ 1 : ℤ[X]) = X ^ 2 - 1 := by ring
  rw [hp]
  norm_num [coeff_sub, coeff_X_pow, coeff_one]
