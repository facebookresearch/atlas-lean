/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularInverseProductMean

/-! # Tests for finite sums in modular inverse product means -/

open Complex Finset MetaMathlibExt

-- For frequency one modulo four the negative phase gives a positive imaginary part.
example : ∑ b ∈ Icc (1 : ℕ) 3, (b : ℂ) * exp (2 * Real.pi * I * (-(b : ℂ)) / 4) =
    -2 + 2 * I := by
  have h := sum_mul_additive_character (q := 4) (k := 1) (by decide) (by decide)
  norm_num only [Nat.cast_ofNat, Nat.cast_one, one_mul, Nat.reduceSub] at h
  rw [h, show 2 * (Real.pi : ℂ) * I * -1 / 4 = -Real.pi / 2 * I by ring,
    exp_neg_pi_div_two_mul_I]
  norm_num [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq_apply]

-- Frequency two modulo four gives a character of order two and weighted sum −2.
example : ∑ b ∈ Icc (1 : ℕ) 3, (b : ℂ) * exp (2 * Real.pi * I * (-(2 * b : ℂ)) / 4) = -2 := by
  have h := sum_mul_additive_character (q := 4) (k := 2) (by decide) (by decide)
  norm_num only [Nat.cast_ofNat, Nat.reduceSub] at h
  rw [h, show 2 * (Real.pi : ℂ) * I * -2 / 4 = -(Real.pi * I) by ring, exp_neg_pi_mul_I]
  norm_num

-- At zero the divisor sum is empty for every summand.
example (f : ℕ → ℂ) :
    (∑ d ∈ (0 : ℕ).divisors, ∑ h ∈ Icc 1 (0 / d) with Nat.Coprime (0 / d) h, f (h * d)) = 0 := by
  rw [← sum_Icc_eq_sum_divisors_coprime]
  simp

-- At modulus four the three gcd classes are {1, 3}, {2}, and {4}.
example (f : ℕ → ℂ) :
    ∑ k ∈ Icc 1 4, f k = (f 1 + f 3) + f 2 + f 4 := by
  rw [sum_Icc_eq_sum_divisors_coprime, show (4 : ℕ).divisors = {1, 2, 4} by decide]
  have h₁ : {h ∈ Icc 1 4 | Nat.Coprime 4 h} = {1, 3} := by decide
  have h₂ : {h ∈ Icc 1 2 | Nat.Coprime 2 h} = {1} := by decide
  have h₄ : {h ∈ Icc 1 1 | Nat.Coprime 1 h} = {1} := by decide
  norm_num [h₁, h₂, h₄, -Nat.coprime_two_left, add_assoc]
