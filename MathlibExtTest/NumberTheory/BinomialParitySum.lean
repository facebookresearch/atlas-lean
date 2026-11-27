/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomialParitySum

open MetaMathlibExt

-- The single term at k = 0 contributes 1 for every m, including m = 0.
example (m : ℕ) :
    ∑ k ∈ Finset.range 1, ((2 ^ m * k).choose k * (0 : ℕ).choose k) % 2 = 1 := by
  simpa only [pow_zero, Nat.sub_self, Nat.zero_add, ite_eq_left (dvd_zero m)] using
    sum_choose_two_pow_mul_mod_two_two_pow_sub_one m 0

-- A positive exponent is outside the multiples of zero.
example : ∑ k ∈ Finset.range 8, (k.choose (7 + k) * (7 : ℕ).choose k) % 2 = 0 := by
  have h : ¬ 0 ∣ (3 : ℕ) := by decide
  simpa only [pow_zero, one_mul, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, ite_eq_right h] using
    sum_choose_two_pow_mul_mod_two_two_pow_sub_one 0 3

-- A shift by one bit contributes 1 for every exponent.
example (ℓ : ℕ) :
    ∑ k ∈ Finset.range (2 ^ ℓ - 1 + 1),
      ((2 * k).choose (2 ^ ℓ - 1 + k) * (2 ^ ℓ - 1).choose k) % 2 = 1 := by
  simpa only [pow_one, ite_eq_left (one_dvd ℓ)] using
    sum_choose_two_pow_mul_mod_two_two_pow_sub_one 1 ℓ

example : ∑ k ∈ Finset.range 8, ((4 * k).choose (7 + k) * (7 : ℕ).choose k) % 2 = 0 := by
  have h : ¬ 2 ∣ (3 : ℕ) := by decide
  simpa only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, ite_eq_right h] using
    sum_choose_two_pow_mul_mod_two_two_pow_sub_one 2 3

example : ∑ k ∈ Finset.range 16, ((4 * k).choose (15 + k) * (15 : ℕ).choose k) % 2 = 1 := by
  have h : 2 ∣ (4 : ℕ) := by decide
  simpa only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, ite_eq_left h] using
    sum_choose_two_pow_mul_mod_two_two_pow_sub_one 2 4

-- Zero has no runs, and a single 1-bit creates no adjacent pair.
example : ((∑ k ∈ Finset.range (0 + 1),
    (Nat.choose 0 (2 * k) * Nat.choose 0 k) % 2 : ℕ) : ℤ) = 1 := by
  rw [runLengthTransform_choose_two_mul_pow_two, runLengthTransform_zero]

example : ((∑ k ∈ Finset.range (8 + 1),
    (Nat.choose 8 (2 * k) * Nat.choose 8 k) % 2 : ℕ) : ℤ) = 1 := by
  rw [runLengthTransform_choose_two_mul_pow_two]
  decide

-- The runs of 110111₂ have different lengths and contribute factors 2 and 4.
example : ((∑ k ∈ Finset.range (55 + 1),
    (Nat.choose 55 (2 * k) * Nat.choose 55 k) % 2 : ℕ) : ℤ) = 8 := by
  rw [runLengthTransform_choose_two_mul_pow_two]
  decide
