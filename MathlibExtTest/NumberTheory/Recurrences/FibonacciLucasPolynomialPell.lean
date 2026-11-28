/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Recurrences.FibonacciLucasPolynomialPell

/-! # Tests for the polynomial Pell classification -/

open MetaMathlibExt Polynomial

-- Use positive parameters with `b ∤ a`, and retain the fractional coefficients.
local notation "A" => (3 : ℚ[X]) * X
local notation "D" => A ^ 2 + 8
local notation "H" => C (1 / 2 : ℚ)
local notation "F" => generalizedFibonacciPolynomial 0 1 (C (3 : ℤ) * X) (C 2)
local notation "L" => generalizedFibonacciPolynomial 2 (C (3 : ℤ) * X) (C (3 : ℤ) * X) (C 2)
local notation "rat" => Polynomial.map (Int.castRingHom ℚ)

private theorem two_mul_half : (2 : ℚ[X]) * H = 1 := by
  rw [← map_ofNat C, ← C_mul]
  norm_num

private theorem four_mul_half_sq : (4 : ℚ[X]) * H ^ 2 = 1 := by
  calc
    _ = (2 * H) ^ 2 := by ring
    _ = 1 := by rw [two_mul_half, one_pow]

-- The zero-Q pair has index zero and parity zero.
example : (2 : ℚ[X]) ^ 2 - D * 0 ^ 2 = 4 ∧ rat (L 0) = 2 ∧ rat (F 0) = 0 ∧
    (0 : ℕ) % 2 = 0 := by
  norm_num [generalizedFibonacciPolynomial_zero]

-- The nonzero constant-Q pair has index one and parity one.
example : A ^ 2 - D * 1 ^ 2 = -8 ∧ rat (L 1) = A ∧ rat (F 1) = 1 ∧ (1 : ℕ) % 2 = 1 := by
  refine ⟨by ring, ?_, ?_, by decide⟩ <;> norm_num [generalizedFibonacciPolynomial_one]

local notation "P₂" => H * (A ^ 2 + 4)
local notation "Q₂" => H * A
local notation "P₃" => H * (A ^ 3 + 6 * A)
local notation "Q₃" => H * (A ^ 2 + 2)

-- At index two, rescaling a rational pair by two gives the recurrence values.
example : P₂ ^ 2 - D * Q₂ ^ 2 = 4 ∧
    2 * P₂ = rat (L 2) ∧ 2 * Q₂ = rat (F 2) ∧ (2 : ℕ) % 2 = 0 := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · linear_combination 4 * four_mul_half_sq
  · rw [← mul_assoc, two_mul_half, one_mul]
    change _ = rat (L (0 + 2))
    norm_num [generalizedFibonacciPolynomial_add_two]
    ring
  · rw [← mul_assoc, two_mul_half, one_mul]
    change _ = rat (F (0 + 2))
    norm_num [generalizedFibonacciPolynomial_add_two]

private theorem odd_pair_pell : P₃ ^ 2 - D * Q₃ ^ 2 = -8 := by
  linear_combination -8 * four_mul_half_sq

-- The first nonconstant odd pair also has scale two, but a negative Pell constant.
example : P₃ ^ 2 - D * Q₃ ^ 2 = -8 ∧
    2 * P₃ = rat (L 3) ∧ 2 * Q₃ = rat (F 3) ∧ (3 : ℕ) % 2 = 1 := by
  refine ⟨odd_pair_pell, ?_, ?_, by decide⟩
  · rw [← mul_assoc, two_mul_half, one_mul]
    change _ = rat (L (1 + 2))
    norm_num [generalizedFibonacciPolynomial_add_two]
    ring
  · rw [← mul_assoc, two_mul_half, one_mul]
    change _ = rat (F (1 + 2))
    norm_num [generalizedFibonacciPolynomial_add_two]
    ring

-- A client of the public theorem, using the independently checked odd pair.
example : ∃ n : ℕ, C ((2 : ℚ) ^ (n / 2)) * P₃ = rat (L n) ∧
    C ((2 : ℚ) ^ (n / 2)) * Q₃ = rat (F n) ∧ n % 2 = 1 := by
  have hA : natDegree A = 1 := by
    rw [← map_ofNat C 3]
    exact natDegree_C_mul_X _ (by norm_num)
  have hleadA : leadingCoeff A = 3 := by
    rw [← map_ofNat C 3, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X, mul_one]
  refine fibLucasPoly_of_pell_eq (a := 3) (b := 2) (r₀ := 1) (by decide) (by decide) ?_ ?_
    (by decide) ?_
  · rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_add_of_degree_lt' (degree_lt_degree ?_)]
    · norm_num [leadingCoeff_pow, hleadA]
    · have h := natDegree_mul_le (p := (6 : ℚ[X])) (q := A)
      norm_num [natDegree_pow, hA] at h ⊢
      omega
  · rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_add_of_degree_lt' (degree_lt_degree ?_)]
    · norm_num [leadingCoeff_pow, hleadA]
    · norm_num [natDegree_pow, hA]
  · have hD : C ((↑(3 : ℕ) : ℚ) ^ 2) * X ^ 2 + C (4 * (↑(2 : ℕ) : ℚ)) = D := by
      rw [C_pow, mul_pow]
      norm_num [map_ofNat]
    rw [hD]
    convert odd_pair_pell using 1
    norm_num [map_neg, map_ofNat]
