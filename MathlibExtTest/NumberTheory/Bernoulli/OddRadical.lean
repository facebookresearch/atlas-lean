/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.OddRadical

open MetaMathlibExt UniqueFactorizationMonoid

-- The predecessor of the exceptional index 2 fails the radical equality.
-- At the upper end of the list the radical equality holds at 59.
example : bernoulliDiffDenominator 1 ≠ radical (1 + 1 : ℕ) ∧
    bernoulliDiffDenominator 59 = radical (59 + 1 : ℕ) := by
  simp only [Nat.radical_eq_prod_primeFactors]
  decide +kernel

-- Check the exceptional index 2 and the shift from the last odd solution to its successor.
example (h : {n : ℕ | 1 ≤ n ∧ bernoulliDiffDenominator n = radical (n + 1) ∧ Odd n} =
    {3, 5, 9, 11, 27, 29, 35, 59}) :
    2 ∈ bernoulliIntegralDerivativeIndices 1 ∧ 59 ∉ bernoulliIntegralDerivativeIndices 1 ∧
      60 ∈ bernoulliIntegralDerivativeIndices 1 := by
  rw [odd_radical_conjecture_implies_bernoulli_integral_derivative_conjecture h]
  decide

-- In base 10, 19 has last digit 9 = 10 - 1, so its digit sum 1 + 9 reaches the base.
example : 10 ≤ (Nat.digits 10 19).sum :=
  le_digit_sum_of_last_digit (by decide) (by decide) (by decide)
