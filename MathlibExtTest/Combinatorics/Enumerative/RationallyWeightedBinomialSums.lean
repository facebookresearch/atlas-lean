/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RationallyWeightedBinomialSums
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.RationallyWeightedBinomialSums` -/

namespace MathlibExtTest.RationallyWeightedBinomialSums

open MetaMathlibExt

-- Edge case `n = 0`: the only term is `binom(0, 0) / 1 = 1`, and `(2 ^ 1 - 1) / 1 = 1`.
example : ∑ k ∈ Finset.range (0 + 1), ((0 : ℕ).choose k : ℚ) / (k + 1) = 1 := by
  rw [sum_choose_div_succ]
  norm_num

-- Row `n = 4`, summed term by term without the theorem:
-- `1/1 + 4/2 + 6/3 + 4/4 + 1/5 = 31/5 = (2 ^ 5 - 1) / 5`.
example : ∑ k ∈ Finset.range (4 + 1), ((4 : ℕ).choose k : ℚ) / (k + 1) = 31 / 5 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

-- The same value from the theorem.
example : ∑ k ∈ Finset.range (4 + 1), ((4 : ℕ).choose k : ℚ) / (k + 1) = 31 / 5 := by
  rw [sum_choose_div_succ]
  norm_num

-- Clearing the denominator: `(n + 1) ∑_{k=0}^n binom(n, k) / (k + 1) = 2 ^ (n + 1) - 1`.
example (n : ℕ) :
    ((n : ℚ) + 1) * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) / (k + 1) = 2 ^ (n + 1) - 1 := by
  rw [sum_choose_div_succ]
  field_simp

-- The identity in `ℝ`, by casting the rational identity.
example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) / (k + 1) = (2 ^ (n + 1) - 1) / (n + 1) := by
  have h := congrArg (Rat.cast : ℚ → ℝ) (sum_choose_div_succ n)
  push_cast at h
  exact_mod_cast h

-- The sum is empty at N = 0, and it is negative at N = 1.
example :
    ∑ k ∈ Finset.Icc 1 0,
      (-1 : ℤ) ^ k * ((0 : ℕ).choose k : ℤ) * 2 ^ (0 - k) * (k : ℤ) ^ 2 = 0 :=
  (sum_neg_one_pow_choose_two_pow_mul_sq 0).trans (by decide)

example :
    ∑ k ∈ Finset.Icc 1 1,
      (-1 : ℤ) ^ k * ((1 : ℕ).choose k : ℤ) * 2 ^ (1 - k) * (k : ℤ) ^ 2 = -1 :=
  (sum_neg_one_pow_choose_two_pow_mul_sq 1).trans (by decide)

-- At N = 3 the three terms give -12 + 24 - 9 = 3.
example :
    ∑ k ∈ Finset.Icc 1 3,
      (-1 : ℤ) ^ k * ((3 : ℕ).choose k : ℤ) * 2 ^ (3 - k) * (k : ℤ) ^ 2 = 3 :=
  (sum_neg_one_pow_choose_two_pow_mul_sq 3).trans (by decide)

-- Rows zero and one give the empty sum and a single term, respectively.
example : ∑ k ∈ Finset.Icc 1 0, (-1 : ℚ) ^ (k - 1) * (0 : ℕ).choose k / k = 0 :=
  (sum_neg_one_pow_choose_div_eq_harmonic 0).trans harmonic_zero

example : ∑ k ∈ Finset.Icc 1 1, (-1 : ℚ) ^ (k - 1) * (1 : ℕ).choose k / k = 1 := by
  rw [sum_neg_one_pow_choose_div_eq_harmonic]
  norm_num [harmonic, Finset.sum_range_succ]

-- Row four includes both signs and sums to 4 - 6/2 + 4/3 - 1/4 = 25/12.
example :
    ∑ k ∈ Finset.Icc 1 4, (-1 : ℚ) ^ (k - 1) * (4 : ℕ).choose k / k = 25 / 12 := by
  rw [sum_neg_one_pow_choose_div_eq_harmonic]
  norm_num [harmonic, Finset.sum_range_succ]

-- Independently evaluate the alternating sum in row four.
example :
    ∑ k ∈ Finset.Icc 1 4, (-1 : ℚ) ^ (k - 1) * (4 : ℕ).choose k / k = 25 / 12 := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  norm_num [Finset.sum_range_succ, Nat.choose]

-- The inverse-square sum is empty at zero.
example : ∑ k ∈ Finset.Icc 1 0, (-1 : ℚ) ^ (k - 1) * (0 : ℕ).choose k / (k : ℚ) ^ 2 = 0 := by
  rw [sum_neg_one_pow_choose_div_sq_eq_sum_harmonic]
  simp

-- At two the first negative term contributes, giving 2 - 1/4 = 7/4.
example : ∑ k ∈ Finset.Icc 1 2, (-1 : ℚ) ^ (k - 1) * (2 : ℕ).choose k / (k : ℚ) ^ 2 = 7 / 4 := by
  rw [sum_neg_one_pow_choose_div_sq_eq_sum_harmonic]
  rw [show Finset.Icc 1 2 = {1, 2} from by decide]
  norm_num [harmonic, Finset.sum_range_succ]

-- The inverse-square polynomial sum is empty at n = 0, for every x.
example (x : ℝ) :
    ∑ k ∈ Finset.Icc 1 0, ((0 : ℕ).choose k : ℝ) * x ^ k / (k : ℝ) ^ 2 = 0 := by
  rw [sum_choose_mul_pow_div_sq]
  simp

-- At x = 0, the two nested sums agree for every n.
example (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (n.choose k : ℝ) * (0 : ℝ) ^ k / (k : ℝ) ^ 2 = 0 := by
  rw [sum_choose_mul_pow_div_sq]
  simp

-- At n = 2 and x = -1 the identity gives -2 + 1/4 = -7/4.
example :
    ∑ k ∈ Finset.Icc 1 2, ((2 : ℕ).choose k : ℝ) * (-1 : ℝ) ^ k / (k : ℝ) ^ 2 = -7 / 4 := by
  rw [sum_choose_mul_pow_div_sq]
  simp only [show Finset.Icc 1 2 = {1, 2} from by decide, Finset.sum_insert (by decide :
    (1 : ℕ) ∉ ({2} : Finset ℕ)), Finset.sum_singleton, Finset.Icc_self]
  norm_num

-- Exponent zero recovers the unweighted sum, including the zero-index term.
example (N : ℕ) : ∑ k ∈ Finset.range (N + 1), N.choose k * Nat.fib k = Nat.fib (2 * N) := by
  simpa using sum_pow_mul_choose_mul_fib N 0

-- At exponent five in row two, the falling factorials above order two vanish.
example : ∑ k ∈ Finset.range (2 + 1), k ^ 5 * (2 : ℕ).choose k * Nat.fib k = 34 :=
  (sum_pow_mul_choose_mul_fib 2 5).trans (by decide)

-- The first-power sum is empty in row zero.
example : ∑ k ∈ Finset.Icc 1 0, k * (0 : ℕ).choose k * Nat.fib k = 0 :=
  (sum_pow_mul_choose_mul_fib_small 0).1.trans (by decide)

-- In row one the higher falling factorials vanish, including those with truncated indices.
example : ∑ k ∈ Finset.Icc 1 1, k ^ 4 * (1 : ℕ).choose k * Nat.fib k = 1 :=
  (sum_pow_mul_choose_mul_fib_small 1).2.2.2.trans (by decide)

-- Row four is the first where all four terms of the fourth-power formula contribute.
example : ∑ k ∈ Finset.Icc 1 4, k ^ 4 * (4 : ℕ).choose k * Nat.fib k = 1516 :=
  (sum_pow_mul_choose_mul_fib_small 4).2.2.2.trans (by decide)

-- At x = r = 0, the constant coefficient survives by the convention 0^0 = 1.
example (a : ℕ → ℝ) :
    ∑ k ∈ Finset.range (2 + 1), (k : ℝ) ^ (0 : ℕ) * a k * (0 : ℝ) ^ k = a 0 := by
  rw [sum_pow_mul_coeff_eq_sum_stirlingSecond_derivative]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond, Polynomial.eval_add, Polynomial.eval_mul]

-- At x = 0 and positive weight exponent, even the constant coefficient contributes zero.
example (a : ℕ → ℝ) :
    ∑ k ∈ Finset.range (2 + 1), (k : ℝ) ^ (2 : ℕ) * a k * (0 : ℝ) ^ k = 0 := by
  rw [sum_pow_mul_coeff_eq_sum_stirlingSecond_derivative]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

-- For 1 + X + X² at x = -2 and r = 3, the third derivative vanishes;
-- the two lower positive-order terms give 6 + 24 = 30.
example : ∑ k ∈ Finset.range (2 + 1), (k : ℝ) ^ (3 : ℕ) * 1 * (-2 : ℝ) ^ k = 30 := by
  rw [sum_pow_mul_coeff_eq_sum_stirlingSecond_derivative (fun _ => 1) 2 3 (-2)]
  simp only [Polynomial.iterate_derivative_sum, Polynomial.eval_finsetSum,
    Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_C_mul,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond, Nat.descFactorial]

end MathlibExtTest.RationallyWeightedBinomialSums
