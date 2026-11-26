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

-- At exponent zero the binomial sum advances any solution by twice the row index.
example (a b : ℝ) (W : ℕ → ℝ) (hW : ∀ n, W (n + 2) = a * W (n + 1) + b * W n) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * a ^ k * b ^ (N - k) * W k = W (2 * N) := by
  simpa using sum_pow_mul_choose_mul_secondOrder a b W hW N 0

-- Wₖ = k has a repeated characteristic root for a = 2 and b = -1.
-- At N = 2 and r = 5 the nonzero terms are -4 and 256, and orders above two vanish.
example : ∑ k ∈ Finset.range (2 + 1),
    (k : ℝ) ^ (5 : ℕ) * (2 : ℕ).choose k * 2 ^ k * (-1) ^ (2 - k) * k = 252 := by
  have hW (n : ℕ) : ((n + 2 : ℕ) : ℝ) = 2 * (n + 1 : ℕ) + (-1) * n := by
    push_cast
    ring
  apply (sum_pow_mul_choose_mul_secondOrder 2 (-1) (fun k ↦ (k : ℝ)) hW 2 5).trans
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond, Nat.descFactorial]

-- Exponent zero retains the nonzero L₀ term and recovers the unweighted Lucas sum.
example (N : ℕ) : ∑ k ∈ Finset.range (N + 1), N.choose k * lucasNumber k = lucasNumber (2 * N) := by
  simpa using sum_pow_mul_choose_mul_lucasNumber N 0

-- At N = 0 the exponent-zero sum is L₀ = 2, but a positive exponent gives zero.
example : ∑ k ∈ Finset.range (0 + 1), k ^ (0 : ℕ) * (0 : ℕ).choose k * lucasNumber k = 2 :=
  (sum_pow_mul_choose_mul_lucasNumber 0 0).trans (by decide)

example : ∑ k ∈ Finset.range (0 + 1), k ^ (1 : ℕ) * (0 : ℕ).choose k * lucasNumber k = 0 :=
  (sum_pow_mul_choose_mul_lucasNumber 0 1).trans (by decide)

-- At N = 2 and r = 5, orders above two vanish even when the index 2N - i truncates.
example : ∑ k ∈ Finset.range (2 + 1), k ^ (5 : ℕ) * (2 : ℕ).choose k * lucasNumber k = 98 :=
  (sum_pow_mul_choose_mul_lucasNumber 2 5).trans (by decide)

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

-- Distinct roots 2 and -1 with Binet coefficients 2 and 3 give U₀ = 5, U₁ = 1, U₂ = 11.
private noncomputable def sampleSequence (k : ℕ) : ℝ :=
  2 * 2 ^ k + 3 * (-1) ^ k

private theorem sampleSequence_rec (n : ℕ) :
    sampleSequence (n + 2) = 1 * sampleSequence (n + 1) + 2 * sampleSequence n := by
  simp only [sampleSequence, pow_add, pow_one]
  ring

-- h(k) = 1 + k + k² + k³; in row two the order-three factorial vanishes.
-- At x = -1 the three terms on the left are 25 - 8 + 1815 = 1832.
example : ∑ k ∈ Finset.range (2 + 1),
    (∑ j ∈ Finset.range (3 + 1), (1 : ℂ) * (k : ℂ) ^ j) *
      (2 : ℕ).choose k * (sampleSequence k : ℂ) ^ (2 : ℕ) * (-1 : ℂ) ^ k = 1832 := by
  apply (sum_poly_mul_choose_mul_secondOrder_pow 1 2 sampleSequence sampleSequence_rec
    2 (-1) (by norm_num) (by norm_num) (by norm_num) (fun _ => 1) 3 2 2 (-1)).trans
  norm_num [sampleSequence, Finset.sum_range_succ, Nat.choose, Nat.stirlingSecond, Nat.descFactorial,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg]

-- Row zero with a constant weight keeps the k = 0 term, even at x = 0.
example : ∑ k ∈ Finset.range (0 + 1),
    (∑ j ∈ Finset.range (0 + 1), (2 : ℂ) * (k : ℂ) ^ j) *
      (0 : ℕ).choose k * (sampleSequence k : ℂ) ^ (2 : ℕ) * (0 : ℂ) ^ k = 50 := by
  apply (sum_poly_mul_choose_mul_secondOrder_pow 1 2 sampleSequence sampleSequence_rec
    2 (-1) (by norm_num) (by norm_num) (by norm_num) (fun _ => 2) 0 0 2 0).trans
  norm_num [sampleSequence, Finset.sum_range_succ, Nat.choose, Nat.stirlingSecond, Nat.descFactorial,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg]

-- With r = 0 even the zero sequence has unit weight from Uₖ^r; one characteristic root is zero.
example : ∑ k ∈ Finset.range (1 + 1),
    (∑ j ∈ Finset.range (1 + 1), (1 : ℂ) * (k : ℂ) ^ j) *
      (1 : ℕ).choose k * (0 : ℂ) ^ (0 : ℕ) * (2 : ℂ) ^ k = 5 := by
  apply (sum_poly_mul_choose_mul_secondOrder_pow 1 0 (fun _ => 0) (by simp)
    1 0 (by norm_num) (by norm_num) (by norm_num) (fun _ => 1) 1 1 0 2).trans
  norm_num [Finset.sum_range_succ, Nat.choose, Nat.stirlingSecond, Nat.descFactorial]

end MathlibExtTest.RationallyWeightedBinomialSums
