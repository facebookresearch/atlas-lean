/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.KFibonacciAlternatingBinomial

/-! # Tests for binomial formulas for the k-Fibonacci numbers -/

open MetaMathlibExt

-- The index excluded in Farhi's statement is the last one with an empty correction sum.
example (k : ℕ) (hk : 2 ≤ k) (F : ℕ → ℤ) (hF0 : ∀ i < k - 1, F i = 0)
    (hF1 : F (k - 1) = 1) (hrec : ∀ m, F (m + k) = ∑ i ∈ Finset.range k, F (m + i)) :
    (F (2 * k - 1) : ℚ) = 2 ^ (k - 1) := by
  rw [kFibonacci_eq_alternating_binomial_sum k _ hk (by omega) F hF0 hF1 hrec,
    show 2 * k - 1 - k + 1 = k by omega, Nat.div_eq_of_lt (Nat.lt_succ_self k),
    show 2 * k - 1 - k = k - 1 by omega]
  simp

-- For the tribonacci numbers the second correction first appears at n = 10,
-- where its power of two is a reciprocal.
example (F : ℕ → ℤ) (hF0 : ∀ i < 2, F i = 0) (hF1 : F 2 = 1)
    (hrec : ∀ m, F (m + 3) = ∑ i ∈ Finset.range 3, F (m + i)) :
    (F 10 : ℚ) = 81 := by
  rw [kFibonacci_eq_alternating_binomial_sum 3 10 (by decide) (by decide) F hF0 hF1 hrec]
  rw [show Finset.Icc 1 ((10 - 3 + 1) / (3 + 1)) = {1, 2} by decide]
  have hchoose : Ring.choose (3 : ℤ) 2 = 3 := Ring.choose_natCast (R := ℤ) 3 2
  norm_num [hchoose]

-- At n = k the sum consists only of the constant term.
example (k : ℕ) (hk : 2 ≤ k) (F : ℕ → ℤ) (hF0 : ∀ i < k - 1, F i = 0)
    (hF1 : F (k - 1) = 1) (hrec : ∀ m, F (m + k) = ∑ i ∈ Finset.range k, F (m + i)) :
    (F k : ℚ) = 1 := by
  rw [kFibonacci_eq_binomial_sum k k hk le_rfl F hF0 hF1 hrec, Nat.sub_self]
  have hdiv : 1 / (k + 1) = 0 := Nat.div_eq_of_lt (by omega)
  simp [hdiv]

-- At n = 6 the tribonacci sum first includes the index-one term.
example (F : ℕ → ℤ) (hF0 : ∀ i < 2, F i = 0) (hF1 : F 2 = 1)
    (hrec : ∀ m, F (m + 3) = ∑ i ∈ Finset.range 3, F (m + i)) :
    (F 6 : ℚ) = 7 := by
  rw [kFibonacci_eq_binomial_sum 3 6 (by decide) (by decide) F hF0 hF1 hrec]
  rw [show (6 - 3 + 1) / (3 + 1) + 1 = 2 by decide]
  norm_num [Finset.sum_range_succ]

-- At n = 10 there are two nonconstant terms, including a coefficient at lower index two.
example (F : ℕ → ℤ) (hF0 : ∀ i < 2, F i = 0) (hF1 : F 2 = 1)
    (hrec : ∀ m, F (m + 3) = ∑ i ∈ Finset.range 3, F (m + i)) :
    (F 10 : ℚ) = 81 := by
  rw [kFibonacci_eq_binomial_sum 3 10 (by decide) (by decide) F hF0 hF1 hrec]
  rw [show (10 - 3 + 1) / (3 + 1) + 1 = 3 by decide]
  have hchoose : Ring.choose (-1 : ℤ) 2 = 1 := by
    have hpascal := Ring.choose_succ_succ (-1 : ℤ) 1
    norm_num at hpascal
    omega
  norm_num [Finset.sum_range_succ, hchoose]
