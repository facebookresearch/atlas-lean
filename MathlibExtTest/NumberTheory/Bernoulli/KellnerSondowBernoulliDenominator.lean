/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.KellnerSondowBernoulliDenominator

open MetaMathlibExt Polynomial

example (n : ℕ) (hn : 1 ≤ n) :
    bernoulliDiffDenominator n =
      polynomialDenominator (Polynomial.bernoulli n - C (_root_.bernoulli n)) :=
  bernoulliDiffDenominator_eq_polynomialDenominator n hn

-- At the lower endpoint the difference is integral.
example : polynomialDenominator (Polynomial.bernoulli 1 - C (_root_.bernoulli 1)) = 1 := by
  rw [← bernoulliDiffDenominator_eq_polynomialDenominator 1 le_rfl]
  decide

-- Subtracting the constant term at n = 2 removes both prime factors of its denominator.
example : polynomialDenominator (Polynomial.bernoulli 2 - C (_root_.bernoulli 2)) = 1 ∧
    (_root_.bernoulli 2).den = 6 := by
  constructor
  · rw [← bernoulliDiffDenominator_eq_polynomialDenominator 2 (by decide)]
    decide
  · norm_num [_root_.bernoulli_two]

-- Both 2 and 3 occur in the denominator at n = 5.
example : polynomialDenominator (Polynomial.bernoulli 5 - C (_root_.bernoulli 5)) = 6 := by
  rw [← bernoulliDiffDenominator_eq_polynomialDenominator 5 (by decide)]
  decide

-- A prime in the product can also divide the index: 2 divides n = 6.
example : polynomialDenominator (Polynomial.bernoulli 6 - C (_root_.bernoulli 6)) = 2 := by
  rw [← bernoulliDiffDenominator_eq_polynomialDenominator 6 (by decide)]
  decide
