/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Cast.Field
public import MathlibExt.NumberTheory.SZumkeller

/-!
# Harmonic mean of squared divisors of even s-Zumkeller numbers

The harmonic mean of the squared divisors of an even s-Zumkeller number is at most `2τ(n)/3`
(`harmonicMeanSq_le_of_isSZumkeller`).

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller Numbers*,
INTEGERS 24 (2024), Article A95, Proposition 9.
-/

namespace MetaMathlibExt

/-- **Harmonic mean of squared divisors of even s-Zumkeller numbers.** Let $n$ be an even
s-Zumkeller number and let $\tau(n)$ be the number of positive divisors of $n$. Then
$\tau(n) / \sum_{d \mid n} d^{-2} \le 2\tau(n)/3$, where the sum runs over the positive divisors
$d$ of $n$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 9. -/
public theorem harmonicMeanSq_le_of_isSZumkeller (n : ℕ) (h : IsSZumkeller n)
    (he : Even n) :
    (n.divisors.card : ℚ) / ∑ d ∈ n.divisors, 1 / (d : ℚ) ^ 2 ≤ 2 * n.divisors.card / 3 := by
  have hcopy := h
  obtain ⟨A, hA, hne, _, _⟩ := hcopy
  have hn1 : 1 < n := Nat.nonempty_properDivisors.mp (hne.mono hA)
  have hn₀ : n ≠ 0 := by omega
  have hn_pos : 0 < n := by omega
  obtain ⟨S, _, hS⟩ := (isSZumkeller_iff_of_even n hn_pos he).mp h
  have hnonneg : 0 ≤ ∑ d ∈ S, (d : ℤ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hlower : 3 * (n : ℚ) ^ 2 ≤ 2 * ArithmeticFunction.sigma 2 n := by
    exact_mod_cast (show 3 * (n : ℤ) ^ 2 ≤ 2 * ArithmeticFunction.sigma 2 n by omega)
  have hsigma : (ArithmeticFunction.sigma 2 n : ℚ)
      = (n : ℚ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℚ) ^ 2 := by
    rw [ArithmeticFunction.sigma_eq_sum_div, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.cast_pow, Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd), div_pow,
      div_eq_mul_one_div]
  have hsum_lb : 1 ≤ ∑ d ∈ n.divisors, 1 / (d : ℚ) ^ 2 := calc
    1 = 1 / (1 : ℚ) ^ 2 := by norm_num
    _ ≤ _ := Finset.single_le_sum (f := fun d : ℕ => 1 / (d : ℚ) ^ 2)
      (fun d _ => div_nonneg zero_le_one (sq_nonneg _)) (Nat.one_mem_divisors.mpr hn₀)
  have hS_pos : 0 < ∑ d ∈ n.divisors, 1 / (d : ℚ) ^ 2 :=
    lt_of_lt_of_le zero_lt_one hsum_lb
  have hcard_pos : 0 < (n.divisors.card : ℚ) := by
    have hne' : n.divisors.Nonempty := ⟨1, Nat.one_mem_divisors.mpr hn₀⟩
    exact_mod_cast Finset.card_pos.mpr hne'
  have hnQ_pos : (0 : ℚ) < n := by exact_mod_cast hn_pos
  have hn2_pos : (0 : ℚ) < (n : ℚ) ^ 2 := pow_pos hnQ_pos 2
  have h3le : (3 : ℚ) ≤ 2 * ∑ d ∈ n.divisors, 1 / (d : ℚ) ^ 2 := by
    have hl := hlower
    rw [hsigma] at hl
    have h' : (n : ℚ) ^ 2 * 3 ≤ (n : ℚ) ^ 2 * (2 * ∑ d ∈ n.divisors, 1 / (d : ℚ) ^ 2) := by
      linarith
    exact le_of_mul_le_mul_left h' hn2_pos
  rw [div_le_div_iff₀ hS_pos (by norm_num)]
  have hτ_nonneg : (0 : ℚ) ≤ n.divisors.card := le_of_lt hcard_pos
  have hmul := mul_le_mul_of_nonneg_right h3le hτ_nonneg
  linarith

end MetaMathlibExt
