/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SZumkeller

/-! # Tests for s-Zumkeller numbers -/

open MetaMathlibExt

-- The empty product has value one when n = 1.
example : (ArithmeticFunction.sigma 1 1 : ℚ) = 1 := by
  have h := (sigma_one_prod_formulas 1 (by decide)).1
  rw [Nat.primeFactors_one, Finset.prod_empty] at h
  exact h

-- For 12 = 2² · 3, the strict bound uses both prime factors.
example : (ArithmeticFunction.sigma 1 12 : ℚ) / 12 <
    ∏ p ∈ (12 : ℕ).primeFactors, (p : ℚ) / (p - 1) :=
  (sigma_one_prod_formulas 12 (by decide)).2.2 (by decide)

-- Reinserting 30 into this witness gives the equal-squares part {1, 2, 5, 30}.
example : IsSZumkeller 60 := by
  apply (isSZumkeller_iff_of_even 60 (by decide) (by decide)).2
  exact ⟨{1, 2, 5}, by decide, by decide⟩

-- For the smallest positive even integer the right-hand side is negative.
example : ¬ IsSZumkeller 2 := by
  intro h
  obtain ⟨S, _, hsum⟩ := (isSZumkeller_iff_of_even 2 (by decide) (by decide)).1 h
  have hneg : 4 * (∑ d ∈ S, d ^ 2 : ℤ) < 0 := hsum.trans_lt (by decide)
  exact hneg.not_ge (mul_nonneg (by decide) (Finset.sum_nonneg fun d _ => sq_nonneg (d : ℤ)))

-- At α = 3 the proper divisors 5, 15, and 60 have squared sum 3850, half the total.
example : ((120 : ℕ).divisors.card : ℚ) / ∑ d ∈ (120 : ℕ).divisors, 1 / (d : ℚ) ^ 2 <
    512 / 3 := by
  apply harmonicMeanSq_lt_of_isSZumkeller_mersenne 3 120 (by decide) (by decide)
  exact ⟨{5, 15, 60}, by decide, by decide, by decide, by decide⟩

-- An entire even residue class is excluded by the divisibility condition.
example (k : ℕ) : ¬ IsSZumkeller (6 * k + 2) := by
  intro h
  have he : Even (6 * k + 2) := ⟨3 * k + 1, by omega⟩
  have := three_dvd_of_isSZumkeller _ h he
  omega
