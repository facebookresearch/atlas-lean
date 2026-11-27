/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Bernoulli
import MathlibExt.NumberTheory.Bernoulli.KanekoBernoulliStirling

/-!
# Consecutive Bernoulli numbers

Farhi's formula expresses the sum of two consecutive Bernoulli numbers as a weighted sum
of Stirling numbers of the second kind.
-/

namespace MetaMathlibExt

open Finset

/-- **Sum of consecutive Bernoulli numbers via Stirling numbers.** For every natural number $n$,
$B_n + B_{n+1} = \sum_{k=0}^{n} (-1)^k \frac{k!}{k+2} S(n,k)$, where $B_n$ are the Bernoulli numbers
with $B_1 = -1/2$ (generating function $t/(e^t - 1)$, the paper's convention) and $S(n,k)$ are the
Stirling numbers of the second kind.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Corollary 2.19
(`integers-2026-A85-cor-2-19`). -/
public theorem bernoulli_add_bernoulli_succ_eq_sum_stirlingSecond (n : ℕ) :
    bernoulli n + bernoulli (n + 1) = ∑ k ∈ range (n + 1),
      (-1 : ℚ) ^ k * (k.factorial : ℚ) / ((k : ℚ) + 2) * (Nat.stirlingSecond n k : ℚ) := by
  let w (k : ℕ) : ℚ := (-1) ^ k * k.factorial / (k + 1)
  have kaneko (m : ℕ) : bernoulli m = ∑ k ∈ range (m + 1), w k * m.stirlingSecond k := by
    rw [kaneko_bernoulli_stirling_sum, ← Ico_succ_right_eq_Icc, sum_Ico_eq_sum_range]
    simp [w, Nat.add_comm 1, div_mul_eq_mul_div]
  -- In the term k * S(n,k), both endpoints vanish when shifting the summation index.
  have shift : ∑ k ∈ range (n + 1),
        w (k + 1) * (k + 1 : ℕ) * n.stirlingSecond (k + 1) =
      ∑ k ∈ range (n + 1), w k * k * n.stirlingSecond k := by
    rw [sum_range_succ _ n, sum_range_succ' (fun k ↦ w k * k * n.stirlingSecond k)]
    simp [Nat.stirlingSecond_eq_zero_of_lt n.lt_succ_self]
  have next : bernoulli (n + 1) = ∑ k ∈ range (n + 1),
      (w k * k + w (k + 1)) * n.stirlingSecond k := by
    rw [kaneko, sum_range_succ' _ (n + 1)]
    simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, mul_zero, add_zero,
      Nat.stirlingSecond_succ_succ, Nat.cast_add _ (Nat.stirlingSecond n _), Nat.cast_mul]
    simp only [mul_add, add_mul, ← mul_assoc, sum_add_distrib, shift]
  rw [kaneko n, next, ← sum_add_distrib]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← add_mul]
  congr 1
  simp only [w, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

end MetaMathlibExt
