/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! # Even- and odd-index binomial sums with odd reciprocal weights -/

@[expose] public section

/-- **Even-index binomial sum with odd reciprocal weights.** For every natural number $n$,
$$\sum_{k=0}^{\lfloor n/2 \rfloor} \frac{1}{2k+1} \binom{n}{2k} = \frac{2^n}{n+1}.$$

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 4 (`integers-2026-A19-prop-4`). -/
theorem MetaMathlibExt.sum_choose_even_div_two_mul_add_one (n : ℕ) :
    ∑ k ∈ Finset.range (n / 2 + 1), (n.choose (2 * k) : ℚ) / (2 * k + 1) =
      2 ^ n / (n + 1) := by
  classical
  let c (j : ℕ) : ℚ := ((n + 1).choose j : ℚ)
  have hall : ∑ j ∈ Finset.range (n + 2), c j = (2 : ℚ) ^ (n + 1) := by
    dsimp only [c]
    exact_mod_cast Nat.sum_range_choose (n + 1)
  have halt : ∑ j ∈ Finset.range (n + 2), (-1 : ℚ) ^ j * c j = 0 := by
    calc
      _ = ((-1 : ℚ) + 1) ^ (n + 1) := by
        simpa only [c, one_pow, mul_one] using (add_pow (-1 : ℚ) 1 (n + 1)).symm
      _ = 0 := by simp
  have hodd : 2 * (∑ j ∈ (Finset.range (n + 2)).filter Odd, c j) = 2 ^ (n + 1) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    calc
      _ = ∑ j ∈ Finset.range (n + 2), (c j - (-1 : ℚ) ^ j * c j) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : Odd j
        · simp only [ite_eq_left hj, hj.neg_one_pow, neg_one_mul, sub_neg_eq_add, two_mul]
        · simp [hj, (Nat.not_odd_iff_even.mp hj).neg_one_pow]
      _ = _ := by rw [Finset.sum_sub_distrib, hall, halt, sub_zero]
  have hindex : (∑ k ∈ Finset.range (n / 2 + 1), c (2 * k + 1)) =
      ∑ j ∈ (Finset.range (n + 2)).filter Odd, c j := by
    refine Finset.sum_bij (fun k _ => 2 * k + 1) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_filter, Finset.mem_range, Nat.odd_iff]
      omega
    · intro a ha b hb hab
      omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range, Nat.odd_iff] at hj
      exact ⟨j / 2, Finset.mem_range.2 (by omega), by omega⟩
    · intro k _
      rfl
  have hhalf : ∑ k ∈ Finset.range (n / 2 + 1), c (2 * k + 1) = 2 ^ n := by
    rw [← hindex, pow_succ, mul_comm ((2 : ℚ) ^ n) 2] at hodd
    exact mul_left_cancel₀ (by norm_num : (2 : ℚ) ≠ 0) hodd
  calc
    _ = ∑ k ∈ Finset.range (n / 2 + 1), c (2 * k + 1) / (n + 1) := by
      apply Finset.sum_congr rfl
      intro k _
      apply (div_eq_div_iff (by positivity) (by positivity)).2
      have h : ((n : ℚ) + 1) * (n.choose (2 * k) : ℚ) =
          c (2 * k + 1) * (2 * (k : ℚ) + 1) := by
        dsimp only [c]
        exact_mod_cast Nat.add_one_mul_choose_eq n (2 * k)
      rwa [mul_comm ((n : ℚ) + 1)] at h
    _ = _ := by simp only [div_eq_mul_inv, ← Finset.sum_mul, hhalf]

namespace MetaMathlibExt

open Finset

/-- **Odd-index binomial sum with odd reciprocal weights.** For every natural number $n$,
$$\sum_{k=1}^{\lceil n/2 \rceil} \frac{1}{2k+1} \binom{n}{2k-1} =
\frac{2^{n+1}}{n+2} - \frac{2^n}{n+1}.$$

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 1, equation (18). The proof uses the
second identity in Proposition 4, the even-index reciprocal sum. -/
theorem sum_choose_odd_div_two_mul_add_one (n : ℕ) :
    ∑ k ∈ Icc 1 ((n + 1) / 2), (n.choose (2 * k - 1) : ℚ) / (2 * k + 1) =
      2 ^ (n + 1) / (n + 2) - 2 ^ n / (n + 1) := by
  classical
  let c (k : ℕ) : ℚ := ((n + 1).choose (2 * k) : ℚ)
  have hindex : ∑ k ∈ range ((n + 1) / 2 + 1), c k =
      ∑ j ∈ (range (n + 2)).filter Even, ((n + 1).choose j : ℚ) := by
    refine sum_bij (fun k _ ↦ 2 * k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [mem_range] at hk
      simp only [mem_filter, mem_range, Nat.even_iff]
      omega
    · intro a _ b _ hab
      omega
    · intro j hj
      simp only [mem_filter, mem_range, Nat.even_iff] at hj
      exact ⟨j / 2, mem_range.2 (by omega), by omega⟩
    · intro k _
      rfl
  -- Adding the ordinary and alternating sums counts the even coefficients twice.
  have hall : ∑ j ∈ range (n + 2), ((n + 1).choose j : ℚ) = 2 ^ (n + 1) := by
    exact_mod_cast Nat.sum_range_choose (n + 1)
  have halt : ∑ j ∈ range (n + 2), (-1 : ℚ) ^ j * ((n + 1).choose j : ℚ) = 0 := by
    exact_mod_cast Int.alternating_sum_range_choose_of_ne (Nat.succ_ne_zero n)
  have hhalf : ∑ k ∈ range ((n + 1) / 2 + 1), c k = (2 : ℚ) ^ n := by
    apply mul_left_cancel₀ (by norm_num : (2 : ℚ) ≠ 0)
    rw [hindex, mul_sum, sum_filter]
    calc
      _ = ∑ j ∈ range (n + 2),
          (((n + 1).choose j : ℚ) + (-1 : ℚ) ^ j * ((n + 1).choose j : ℚ)) := by
        apply sum_congr rfl
        intro j _
        by_cases hj : Even j
        · simp [hj, hj.neg_one_pow, two_mul]
        · simp [hj, (Nat.not_even_iff_odd.mp hj).neg_one_pow]
      _ = _ := by rw [sum_add_distrib, hall, halt, add_zero, pow_succ, mul_comm]
  have hweighted : ∑ k ∈ range ((n + 1) / 2 + 1), c k / (2 * k + 1) =
      2 ^ (n + 1) / (n + 2) := by
    simpa only [c, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      sum_choose_even_div_two_mul_add_one (n + 1)
  have hinterval : insert 0 (Icc 1 ((n + 1) / 2)) = range ((n + 1) / 2 + 1) := by
    ext k
    simp only [mem_insert, mem_Icc, mem_range]
    omega
  -- Reweight each term; the added k = 0 term in the difference is zero.
  have hscaled : (∑ k ∈ Icc 1 ((n + 1) / 2), (n.choose (2 * k - 1) : ℚ) / (2 * k + 1)) *
      (n + 1) = 2 ^ n - 2 ^ (n + 1) / (n + 2) := by
    rw [sum_mul]
    calc
      _ = ∑ k ∈ Icc 1 ((n + 1) / 2), (c k - c k / (2 * k + 1)) := by
        apply sum_congr rfl
        intro k hk
        have hk' : 2 * k - 1 + 1 = 2 * k := by
          have := (mem_Icc.mp hk).1
          omega
        have hc : ((n : ℚ) + 1) * (n.choose (2 * k - 1) : ℚ) = c k * (2 * (k : ℚ)) := by
          dsimp only [c]
          exact_mod_cast (Nat.add_one_mul_choose_eq n (2 * k - 1)).trans (by rw [hk'])
        rw [div_mul_eq_mul_div, mul_comm _ ((n : ℚ) + 1), hc]
        apply (div_eq_iff (by positivity)).2
        rw [sub_mul, div_mul_cancel₀ _ (by positivity)]
        ring
      _ = ∑ k ∈ range ((n + 1) / 2 + 1), (c k - c k / (2 * k + 1)) := by
        rw [← hinterval, sum_insert (by simp)]
        simp
      _ = _ := by rw [sum_sub_distrib, hhalf, hweighted]
  have hm : (n : ℚ) + 1 ≠ 0 := by positivity
  have hm' : (n : ℚ) + 2 ≠ 0 := by positivity
  calc
    _ = ((2 : ℚ) ^ n - 2 ^ (n + 1) / (n + 2)) / (n + 1) := (eq_div_iff hm).2 hscaled
    _ = (2 : ℚ) ^ (n + 1) / (n + 2) - 2 ^ n / (n + 1) := by
      rw [pow_succ]
      field_simp [hm, hm']
      ring

end MetaMathlibExt
