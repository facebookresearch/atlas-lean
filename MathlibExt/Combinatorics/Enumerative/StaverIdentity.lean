/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- **Splitting a power of minus one.** For natural numbers $k \le n$, we have
$(-1)^{n-k} \cdot (-1)^k = (-1)^n$ in $\mathbb{Q}$. -/
theorem staver_sign_mul (n k : ℕ) (hk : k ≤ n) :
    (-1 : ℚ) ^ (n - k) * (-1 : ℚ) ^ k = (-1 : ℚ) ^ n := by
  rw [← pow_add, Nat.sub_add_cancel hk]

/-- **Squares of powers of minus one.** For every natural number $k$, we have
$(-1)^k \cdot (-1)^k = 1$ in $\mathbb{Q}$. -/
theorem staver_sign_sq (k : ℕ) : (-1 : ℚ) ^ k * (-1 : ℚ) ^ k = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨k, rfl⟩

/-- **Reflecting a power of minus one, odd case.** If $n$ is an odd natural number and
$k \le n$ is a natural number, then $(-1)^{n-k} = -(-1)^k$ in $\mathbb{Q}$. -/
theorem staver_sign_odd {n k : ℕ} (hodd : Odd n) (hk : k ≤ n) :
    (-1 : ℚ) ^ (n - k) = -(-1 : ℚ) ^ k := by
  have hmul := staver_sign_mul n k hk
  have hsq := staver_sign_sq k
  have he1 : (-1 : ℚ) ^ n = -1 := hodd.neg_one_pow
  calc (-1 : ℚ) ^ (n - k) = (-1 : ℚ) ^ (n - k) * 1 := (mul_one _).symm
    _ = (-1 : ℚ) ^ (n - k) * ((-1 : ℚ) ^ k * (-1 : ℚ) ^ k) := by rw [hsq]
    _ = ((-1 : ℚ) ^ (n - k) * (-1 : ℚ) ^ k) * (-1 : ℚ) ^ k := by ring
    _ = (-1 : ℚ) ^ n * (-1 : ℚ) ^ k := by rw [hmul]
    _ = -(-1 : ℚ) ^ k := by rw [he1, neg_one_mul]

/-- **Reflecting a power of minus one, even case.** If $n$ is an even natural number and
$k \le n$ is a natural number, then $(-1)^{n-k} = (-1)^k$ in $\mathbb{Q}$. -/
theorem staver_sign_even {n k : ℕ} (heven : Even n) (hk : k ≤ n) :
    (-1 : ℚ) ^ (n - k) = (-1 : ℚ) ^ k := by
  have hmul := staver_sign_mul n k hk
  have hsq := staver_sign_sq k
  have he1 : (-1 : ℚ) ^ n = 1 := heven.neg_one_pow
  calc (-1 : ℚ) ^ (n - k) = (-1 : ℚ) ^ (n - k) * 1 := (mul_one _).symm
    _ = (-1 : ℚ) ^ (n - k) * ((-1 : ℚ) ^ k * (-1 : ℚ) ^ k) := by rw [hsq]
    _ = ((-1 : ℚ) ^ (n - k) * (-1 : ℚ) ^ k) * (-1 : ℚ) ^ k := by ring
    _ = (-1 : ℚ) ^ n * (-1 : ℚ) ^ k := by rw [hmul]
    _ = (-1 : ℚ) ^ k := by rw [he1, one_mul]

/-- **Reflection of the alternating reciprocal binomial sum.** For every natural number $n$,
$\sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k}^{-1} = \sum_{k=0}^{n} (-1)^{k} \binom{n}{k}^{-1}$
in $\mathbb{Q}$. -/
theorem staver_reflect_zero (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) =
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * ((Nat.choose n k : ℚ))⁻¹ := by
  rw [← Finset.sum_range_reflect
    (fun k => (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have e1 : n + 1 - 1 - k = n - k := by omega
  have e2 : n - (n - k) = k := by omega
  have e3 : Nat.choose n (n - k) = Nat.choose n k := Nat.choose_symm hkle
  rw [e1, e2, e3]

/-- **Reflection of the weighted alternating reciprocal binomial sum.** For every natural
number $n$,
$\sum_{k=0}^{n} (-1)^{n-k} \, k \binom{n}{k}^{-1} =
\sum_{k=0}^{n} (-1)^{k} (n-k) \binom{n}{k}^{-1}$ in $\mathbb{Q}$. -/
theorem staver_reflect_one (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) =
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * ((n - k : ℕ) : ℚ) * ((Nat.choose n k : ℚ))⁻¹ := by
  rw [← Finset.sum_range_reflect
    (fun k => (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have e1 : n + 1 - 1 - k = n - k := by omega
  have e2 : n - (n - k) = k := by omega
  have e3 : Nat.choose n (n - k) = Nat.choose n k := Nat.choose_symm hkle
  rw [e1, e2, e3]

/-- **Staver's identity for alternating reciprocal binomial sums.** For a natural number $n$,
let $S_0(n) = \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k}^{-1}$ and
$S_1(n) = \sum_{k=0}^{n} (-1)^{n-k} \, k \binom{n}{k}^{-1}$, computed in $\mathbb{Q}$.
If $n$ is even, then $S_1(n) = \frac{n}{2} S_0(n)$; if $n$ is odd, then $S_0(n) = 0$.

Source: Renzo Sprugnoli, "Alternating Weighted Sums of Inverses of Binomial
Coefficients," Journal of Integer Sequences 15 (2012), Article 12.6.3
(Staver's identity),
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Sprugnoli/sprugnoli6.tex>.
Both parts follow by pairing `k ↔ n - k`: for odd `n`
the pairs cancel, for even `n` they average to `n/2`.
Proves `Wanted` entry `staver_identity`. -/
theorem staver_identity (n : ℕ) :
    (Even n →
      ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹ =
        (n : ℚ) / 2 * ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) ∧
    (Odd n →
      ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹ = 0) := by
  constructor
  · intro heven
    -- double the weighted sum and pair up
    have h2 : 2 * (∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) =
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ k * (n : ℚ) * ((Nat.choose n k : ℚ))⁻¹ := by
      have hexpand : 2 * (∑ k ∈ Finset.range (n + 1),
            (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) =
          ∑ k ∈ Finset.range (n + 1),
            (((-1 : ℚ) ^ (n - k) * (k : ℚ) +
              (-1 : ℚ) ^ k * ((n - k : ℕ) : ℚ)) *
              ((Nat.choose n k : ℚ))⁻¹) := by
        rw [two_mul]
        nth_rewrite 2 [staver_reflect_one]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hexpand]
      apply Finset.sum_congr rfl
      intro k hk
      have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hkn : (k : ℚ) + ((n - k : ℕ) : ℚ) = (n : ℚ) := by
        exact_mod_cast Nat.add_sub_cancel' hkle
      rw [staver_sign_even heven hkle]
      linear_combination ((-1 : ℚ) ^ k * ((Nat.choose n k : ℚ))⁻¹) * hkn
    -- double the scaled unweighted sum to the same target
    have h0 : 2 * ((n : ℚ) / 2 * (∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹)) =
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ k * (n : ℚ) * ((Nat.choose n k : ℚ))⁻¹ := by
      have hmul : 2 * ((n : ℚ) / 2 * (∑ k ∈ Finset.range (n + 1),
            (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹)) =
          2 * ∑ k ∈ Finset.range (n + 1),
            ((n : ℚ) / 2 * ((-1 : ℚ) ^ (n - k) *
              ((Nat.choose n k : ℚ))⁻¹)) := by
        congr 1
        exact Finset.mul_sum _ _ _
      rw [hmul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [staver_sign_even heven hkle]
      ring
    have hdone : 2 * (∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) =
        2 * ((n : ℚ) / 2 * (∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹)) := by
      linarith [h2, h0]
    exact mul_left_cancel₀ (by norm_num : (2 : ℚ) ≠ 0) hdone
  · intro hodd
    have h2 : 2 * (∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) =
        ∑ k ∈ Finset.range (n + 1),
          (((-1 : ℚ) ^ (n - k) + (-1 : ℚ) ^ k) *
            ((Nat.choose n k : ℚ))⁻¹) := by
      rw [two_mul]
      nth_rewrite 2 [staver_reflect_zero]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (((-1 : ℚ) ^ (n - k) + (-1 : ℚ) ^ k) *
          ((Nat.choose n k : ℚ))⁻¹) = 0 := by
      intro k hk
      have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [staver_sign_odd hodd hkle, neg_add_cancel, zero_mul]
    have hS : 2 * (∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) = 0 := by
      rw [h2]
      exact Finset.sum_eq_zero hterm
    linarith

end MetaMathlibExt
