/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentities
import Mathlib.Tactic.NormNum

open MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted

-- At b = 0, the last weight is still 1.
example (a : ℂ) :
    ∑ i ∈ Finset.range 4, (0 : ℂ) ^ (3 - i) * fibAB a 0 (2 * i) = a ^ 5 := by
  calc
    _ = fibAB a 0 3 * fibAB a 0 4 := by
      simpa only [neg_zero] using sum_neg_b_pow_fibAB_even_prod a 0 3
    _ = _ := by simp [fibAB, pow_succ, mul_assoc]

-- The weights include both signs and a factor of 4 for the term at i = 1.
example : ∑ i ∈ Finset.range 4, (-2 : ℂ) ^ (3 - i) * fibAB 1 2 (2 * i) = 15 := by
  rw [sum_neg_b_pow_fibAB_even_prod 1 2 3]
  norm_num [fibAB]

-- Two recurrence steps preserve the Fibonacci and Lucas specializations of the Horadam sequence.
example (a b : ℂ) : fibAB a b 3 = horadamAB a b 0 1 3 := rfl
example (a b : ℂ) : lucasAB a b 3 = horadamAB a b 2 a 3 := rfl

-- At the first index the quotient is the single term of weight one.
example (a b c : ℂ) (hc : c ≠ 0) (h : c ^ 2 - a * c - b ≠ 0) :
    (c ^ 2 - c * fibAB a b 2 - b * fibAB a b 1) / (c ^ 2 - a * c - b) = 1 := by
  simpa using (sum_c_pow_fibAB a b c hc h 1 le_rfl).symm

-- A repeated characteristic root is allowed, and a negative weight alternates the signs.
example : ∑ i ∈ Finset.Icc 1 4, (-2 : ℂ) ^ (4 - i) * fibAB 2 (-1) i = -2 := by
  rw [sum_c_pow_fibAB 2 (-1) (-2) (by norm_num) (by norm_num) 4 (by decide)]
  norm_num [fibAB]

-- With b = 0 and n = 0 the sole term has weight 0^0 in both sums.
example (a : ℂ) (ha : a ≠ 0) :
    (lucasAB a 0 1 - a) / a ^ 2 = 0 ∧ lucasAB a 0 2 / a ^ 2 = 1 := by
  have hΔ : a ^ 2 + 4 * 0 ≠ 0 := by simpa using pow_ne_zero 2 ha
  obtain ⟨hEven, hOdd⟩ := sum_neg_b_pow_fibAB_disc a 0 hΔ 0
  simpa [sub_eq_add_neg] using And.intro hEven.symm hOdd.symm

-- At b = 2 the weights alternate in sign and have distinct magnitudes.
example :
    (∑ i ∈ Finset.range 3, (-2 : ℂ) ^ (2 - i) * fibAB 1 2 (2 * i)) = 3 ∧
    (∑ i ∈ Finset.range 3, (-2 : ℂ) ^ (2 - i) * fibAB 1 2 (2 * i + 1)) = 9 := by
  obtain ⟨hEven, hOdd⟩ := sum_neg_b_pow_fibAB_disc 1 2 (by norm_num) 2
  rw [hEven, hOdd]
  norm_num [lucasAB]

-- The first negative summand distinguishes the even and odd Pell and Pell–Lucas sums.
example :
    (∑ i ∈ Finset.range 2, (-1 : ℂ) ^ i * fibAB 2 1 (2 * i)) = -2 ∧
    (∑ i ∈ Finset.range 2, (-1 : ℂ) ^ i * lucasAB 2 1 (2 * i)) = -4 ∧
    (∑ i ∈ Finset.range 2, (-1 : ℂ) ^ i * fibAB 2 1 (2 * i + 1)) = -4 ∧
    (∑ i ∈ Finset.range 2, (-1 : ℂ) ^ i * lucasAB 2 1 (2 * i + 1)) = -12 := by
  obtain ⟨hPe, hQe, hPo, hQo⟩ := sum_neg_one_pow_pell 1
  rw [hPe, hQe, hPo, hQo]
  norm_num [fibAB, lucasAB]
