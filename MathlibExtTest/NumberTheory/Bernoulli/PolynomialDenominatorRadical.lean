/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.PolynomialDenominatorRadical

open MetaMathlibExt Polynomial UniqueFactorizationMonoid

-- The paper prints part (iii) as "otherwise even"; at n = 2 the product is 1, and the
-- corrected clause gives oddness.
example : Odd (bernoulliDiffDenominatorCoprimePart 2) ∧
    bernoulliDiffDenominatorCoprimePart 2 = 1 :=
  ⟨(bernoulli_polynomial_denominator_rad_even 2 (by norm_num)).2.2.2.2 (Or.inr even_two),
    by decide⟩

-- At the lower endpoint n = 1 the product is odd as well.
example : Odd (bernoulliDiffDenominatorCoprimePart 1) :=
  (bernoulli_polynomial_denominator_rad_even 1 le_rfl).2.2.2.2 (Or.inl rfl)

-- At the odd index 9 the product is even; it equals 10.
example : Even (bernoulliDiffDenominatorCoprimePart 9) ∧
    bernoulliDiffDenominatorCoprimePart 9 = 10 :=
  ⟨(bernoulli_polynomial_denominator_rad_even 9 (by norm_num)).2.2.2.1 (by norm_num)
    (by decide), by decide⟩

-- No Bernoulli polynomial of positive degree has integer coefficients.
example (n : ℕ) (hn : 1 ≤ n) : polynomialDenominator (Polynomial.bernoulli n) ≠ 1 := by
  intro h
  have := (bernoulli_polynomial_denominator_rad_even n hn).2.1
  rw [h] at this
  exact Nat.not_even_one this

example : ∃ i, ((Polynomial.bernoulli 4).coeff i).den ≠ 1 :=
  (bernoulli_polynomial_denominator_rad_even 4 (by norm_num)).2.2.1

-- Being a radical, the denominator of `Bₙ(x)` is squarefree.
example (n : ℕ) (hn : 1 ≤ n) : Squarefree (polynomialDenominator (Polynomial.bernoulli n)) := by
  rw [(bernoulli_polynomial_denominator_rad_even n hn).1]
  exact squarefree_radical

-- The denominator of `Sₙ(x) = (Bₙ₊₁(x) - Bₙ₊₁) / (n + 1)` is even.
example (n : ℕ) (hn : 1 ≤ n) :
    2 ∣ polynomialDenominator
      (C ((n : ℚ) + 1)⁻¹ * (Polynomial.bernoulli (n + 1) - C (_root_.bernoulli (n + 1)))) := by
  obtain ⟨hrad, heven, -⟩ := bernoulli_polynomial_denominator_rad_even n hn
  rw [hrad, even_iff_two_dvd] at heven
  exact heven.trans radical_dvd_self
