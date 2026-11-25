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
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Even-index binomial sums with odd reciprocal weights -/

open Finset

private lemma two_mul_sum_odd_indices (n : ℕ) (f : ℕ → ℚ) :
    2 * (∑ k ∈ range (n / 2 + 1), f (2 * k + 1)) =
      (∑ j ∈ range (n + 2), f j) - ∑ j ∈ range (n + 2), (-1 : ℚ) ^ j * f j := by
  classical
  have hindex : (∑ k ∈ range (n / 2 + 1), f (2 * k + 1)) =
      ∑ j ∈ (range (n + 2)).filter Odd, f j := by
    refine sum_bij (fun k _ => 2 * k + 1) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [mem_range] at hk
      simp only [mem_filter, mem_range, Nat.odd_iff]
      omega
    · intro a _ b _ hab
      omega
    · intro j hj
      simp only [mem_filter, mem_range, Nat.odd_iff] at hj
      exact ⟨j / 2, mem_range.2 (by omega), by omega⟩
    · intro k _
      rfl
  rw [hindex, mul_sum, sum_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  by_cases hj : Odd j
  · simp only [ite_eq_left hj, hj.neg_one_pow, neg_one_mul, sub_neg_eq_add, two_mul]
  · simp [hj, (Nat.not_odd_iff_even.mp hj).neg_one_pow]

private lemma mul_choose_div_succ (n k : ℕ) :
    ((n : ℚ) + 1) * ((n.choose k : ℚ) / (k + 1)) = ((n + 1).choose (k + 1) : ℚ) := by
  have h : ((n : ℚ) + 1) * (n.choose k : ℚ) = ((n + 1).choose (k + 1) : ℚ) * (k + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  rw [mul_div_assoc', h, mul_div_cancel_right₀ _ (by positivity)]

@[expose] public section

/-- **Even-index binomial sum with odd reciprocal weights.** For every natural number $n$,
$$\sum_{k=0}^{\lfloor n/2 \rfloor} \frac{1}{2k+1} \binom{n}{2k} = \frac{2^n}{n+1}.$$

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 4 (`integers-2026-A19-prop-4`). -/
theorem MetaMathlibExt.sum_choose_even_div_two_mul_add_one (n : ℕ) :
    ∑ k ∈ Finset.range (n / 2 + 1), (n.choose (2 * k) : ℚ) / (2 * k + 1) =
      2 ^ n / (n + 1) := by
  let c (j : ℕ) : ℚ := ((n + 1).choose j : ℚ)
  have hall : ∑ j ∈ range (n + 2), c j = (2 : ℚ) ^ (n + 1) := by
    dsimp only [c]
    exact_mod_cast Nat.sum_range_choose (n + 1)
  have halt : ∑ j ∈ range (n + 2), (-1 : ℚ) ^ j * c j = 0 := by
    calc
      _ = ((-1 : ℚ) + 1) ^ (n + 1) := by
        simpa only [c, one_pow, mul_one] using (add_pow (-1 : ℚ) 1 (n + 1)).symm
      _ = 0 := by simp
  have hhalf : 2 * (∑ k ∈ range (n / 2 + 1), c (2 * k + 1)) = 2 * 2 ^ n := by
    rw [two_mul_sum_odd_indices, hall, halt, sub_zero, pow_succ, mul_comm 2]
  apply (mul_right_inj' (show (n : ℚ) + 1 ≠ 0 by positivity)).mp
  rw [mul_sum, mul_div_cancel₀ _ (by positivity)]
  refine Eq.trans (sum_congr rfl fun k _ ↦ ?_) (mul_left_cancel₀ two_ne_zero hhalf)
  simpa only [c, Nat.cast_mul, Nat.cast_ofNat] using mul_choose_div_succ n (2 * k)

/-- **Alternating sum of $\binom{n}{k} 2^{2k}/(k+1)$.** For every natural number $n$, the
following identity holds in $\mathbb{Q}$:
$$\sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} \frac{2^{2k}}{k+1}
= \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{2k} \frac{2^{2k}}{2k+1}.$$

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 6 (`integers-2026-A19-prop-6`). -/
theorem MetaMathlibExt.sum_neg_one_pow_sub_choose_four_pow_div_succ (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * 2 ^ (2 * k) / (k + 1) =
      ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) * 2 ^ (2 * k) / (2 * k + 1) := by
  -- Clear the common scale, then shift to row `n + 1` on both sides.
  apply (mul_right_inj' (show 4 * ((n : ℚ) + 1) ≠ 0 by positivity)).mp
  calc
    _ = ∑ k ∈ range (n + 1),
        (4 : ℚ) ^ (k + 1) * (-1) ^ (n + 1 - (k + 1)) * (n + 1).choose (k + 1) := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ ↦ ?_
      rw [Nat.add_sub_add_right, pow_succ, pow_mul, show (2 : ℚ) ^ 2 = 4 by norm_num]
      calc
        _ = (4 ^ k * 4) * (-1 : ℚ) ^ (n - k) *
            (((n : ℚ) + 1) * ((n.choose k : ℚ) / (k + 1))) := by ring
        _ = _ := by rw [mul_choose_div_succ]
    _ = 3 ^ (n + 1) - (-1 : ℚ) ^ (n + 1) := by
      -- The shifted sum consists of all but the index-zero term of `(4 - 1)^(n + 1)`.
      have h := add_pow (4 : ℚ) (-1) (n + 1)
      rw [show (4 : ℚ) + (-1) = 3 by norm_num, sum_range_succ'] at h
      exact eq_sub_of_add_eq (by simpa only [pow_zero, one_mul, Nat.sub_zero,
        Nat.choose_zero_right, Nat.cast_one, mul_one] using h.symm)
    _ = 2 * (∑ k ∈ range (n / 2 + 1),
        (2 : ℚ) ^ (2 * k + 1) * (n + 1).choose (2 * k + 1)) := by
      -- Subtract the evaluations at `2` and `-2` to retain only the odd indices.
      rw [two_mul_sum_odd_indices n (fun j ↦ (2 : ℚ) ^ j * (n + 1).choose j)]
      have hplus := (add_pow (2 : ℚ) 1 (n + 1)).symm
      have hminus := (add_pow (-2 : ℚ) 1 (n + 1)).symm
      rw [show (2 : ℚ) + 1 = 3 by norm_num] at hplus
      rw [show (-2 : ℚ) + 1 = -1 by norm_num] at hminus
      simp only [one_pow, mul_one] at hplus hminus
      rw [hplus]
      simp only [← mul_assoc, ← mul_pow, show (-1 : ℚ) * 2 = -2 by norm_num, hminus]
    _ = _ := by
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun k _ ↦ ?_
      rw [pow_succ]
      have hshift := mul_choose_div_succ n (2 * k)
      push_cast at hshift
      rw [← hshift]
      ring
