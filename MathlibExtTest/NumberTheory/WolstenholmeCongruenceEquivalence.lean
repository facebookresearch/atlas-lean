/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WolstenholmeCongruenceEquivalence

/-! # Tests for the equivalent forms of Wolstenholme's congruence -/

open MetaMathlibExt

-- Neither comparison at n = 0 requires a positive upper index.
example (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ^ 3 ∣ ((2 * p).choose p : ℤ) - 2 := by
  have hz : (0 : ℕ).choose p = 0 := Nat.choose_eq_zero_of_lt hp.pos
  exact (choose_two_mul_prime_congr_iff_pow_three p 0 k hp hp5).1.mpr (by simp [hz])

-- At k = 0 the third difference is zero, so the reverse implication also applies.
example (p n : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ^ 3 ∣ ((n * p).choose p : ℤ) - n :=
  (choose_two_mul_prime_congr_iff_pow_three p n 0 hp hp5).2.mpr (by simp)

-- The same reverse implication applies when both binomial coefficients at k vanish.
example (p n k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hnk : n < k) :
    (p : ℤ) ^ 3 ∣ ((n * p).choose p : ℤ) - n := by
  apply (choose_two_mul_prime_congr_iff_pow_three p n k hp hp5).2.mpr
  simp [Nat.choose_eq_zero_of_lt hnk, Nat.choose_eq_zero_of_lt (Nat.mul_lt_mul_of_pos_right hnk hp.pos)]

-- Use the forward directions at a noncentral pair, starting from an independently computed value.
example : (5 : ℤ) ^ 3 ∣ ((4 * 5).choose (2 * 5) : ℤ) - (4 : ℕ).choose 2 := by
  have h := choose_two_mul_prime_congr_iff_pow_three 5 4 2 (by decide) (by decide)
  exact h.2.mp (h.1.mp (by decide))
