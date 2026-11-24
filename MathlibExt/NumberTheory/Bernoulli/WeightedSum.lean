/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ZetaValues

/-!
# A weighted Bernoulli sum with factors $1 - 2^j$

Pascal's identity reduces the difference of successive sums to a binomial sum of
Bernoulli numbers. Evaluating the Bernoulli polynomial at $1/2$ gives its weighted part.
-/

namespace MetaMathlibExt

open Finset

/-- Expand $2^n B_n(1/2)$ in the Bernoulli numbers and apply the duplication formula. -/
private theorem sum_choose_bernoulli_two_pow (n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℚ) * bernoulli j * 2 ^ j =
      (2 - (2 : ℚ) ^ n) * bernoulli n := by
  have half : (Polynomial.bernoulli n).eval 2⁻¹ = (2 / 2 ^ n - 1) * bernoulli n := by
    have h := Polynomial.eval_map_apply (p := Polynomial.bernoulli n) (algebraMap ℚ ℝ) 2⁻¹
    simp only [map_inv₀, map_ofNat, eq_ratCast] at h
    change bernoulliFun n 2⁻¹ = _ at h
    rw [bernoulliFun_eval_half] at h
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact h.symm
  calc
    _ = 2 ^ n * (Polynomial.bernoulli n).eval 2⁻¹ := by
      simp only [Polynomial.bernoulli, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
        mul_sum]
      refine sum_congr rfl fun j hj => ?_
      rw [inv_pow_sub₀ (two_ne_zero' ℚ) (mem_range_succ_iff.mp hj)]
      field_simp
    _ = _ := by
      rw [half]
      field_simp

/-- The binomial sum that occurs in the first difference cancels the new endpoint. -/
private theorem sum_choose_bernoulli_weight (n : ℕ) (hn : 0 < n) :
    (∑ j ∈ Icc 1 n, ((n + 1).choose j : ℚ) * bernoulli j * (1 - 2 ^ j)) +
      2 * bernoulli (n + 1) * (1 - 2 ^ (n + 1)) = 0 := by
  have scaled := sum_choose_bernoulli_two_pow (n + 1)
  rw [sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul] at scaled
  have plain := sum_bernoulli (n + 1)
  rw [ite_eq_right (by omega)] at plain
  have interval := sum_range_eq_add_Ico
    (fun j => ((n + 1).choose j : ℚ) * bernoulli j * (1 - 2 ^ j)) (Nat.zero_lt_succ n)
  simp only [Nat.succ_eq_add_one, Ico_add_one_right_eq_Icc, pow_zero, sub_self, mul_zero,
    zero_add] at interval
  rw [← interval]
  simp_rw [mul_sub, mul_one, sum_sub_distrib, plain]
  linear_combination -scaled

/--
**A weighted Bernoulli sum with factors $1 - 2^j$.** Let $B_j$ denote the Bernoulli numbers
with $B_1 = -\tfrac12$. For every positive integer $n$,
$$\sum_{j=1}^{n} \left(\binom{n}{j} + 1\right) \frac{B_j}{j} \left(1 - 2^j\right) = 1.$$

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 2,
equation (14).
-/
public theorem sum_bernoulli_one_sub_two_pow (n : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.Icc 1 n,
      ((n.choose j : ℚ) + 1) * (bernoulli j / (j : ℚ)) *
        (1 - (2 : ℚ) ^ j)) = 1 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    let w (j : ℕ) := bernoulli j / (j : ℚ) * (1 - (2 : ℚ) ^ j)
    simp_rw [mul_assoc] at ih ⊢
    change ∑ j ∈ Icc 1 (n + 1), (((n + 1).choose j : ℚ) + 1) * w j = 1
    have step (j : ℕ) (hj : j ∈ Icc 1 n) :
        (((n + 1).choose j : ℚ) + 1) * w j = ((n.choose j : ℚ) + 1) * w j +
          ((n + 1).choose j : ℚ) * bernoulli j * (1 - 2 ^ j) / (n + 1) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (mem_Icc.mp hj).1)
      have h : (n + 1 : ℚ) * n.choose k = (n + 1).choose (k + 1) * (k + 1 : ℚ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq n k
      simp only [Nat.choose_succ_succ, Nat.cast_add] at h ⊢
      dsimp [w]
      push_cast
      field_simp
      linear_combination bernoulli (k + 1) * (1 - 2 ^ (k + 1)) * h
    rw [sum_Icc_succ_top (by omega), sum_congr rfl step, sum_add_distrib, ih, ← sum_div,
      Nat.choose_self, Nat.cast_one]
    have cancel := sum_choose_bernoulli_weight n hn
    dsimp [w]
    push_cast
    field_simp
    linear_combination cancel

end MetaMathlibExt
