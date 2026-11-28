/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.StirlingSecondExplicit

/-!
# Lee's alternating expansion of Stirling numbers of the second kind

The finite-difference formula turns the signed binomial transform into a reflection of its
summation index.
-/

open Finset

namespace MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

private theorem neg_one_pow_sub_eq_mul {a b : ℕ} (h : b ≤ a) :
    (-1 : ℤ) ^ (a - b) = (-1 : ℤ) ^ a * (-1 : ℤ) ^ b := by
  rw [← pow_add, show a + b = (a - b) + 2 * b by omega, pow_add, pow_mul]
  simp

private theorem factorial_mul_stirlingSecond_eq_sum (m k : ℕ) :
    (m.factorial : ℤ) * (Nat.stirlingSecond k m : ℤ) =
      ∑ j ∈ range (m + 1), (-1 : ℤ) ^ (m - j) * (Nat.choose m j : ℤ) * (j : ℤ) ^ k := by
  exact_mod_cast (mul_comm _ _).trans (MetaMathlibExt.stirlingSecond_mul_factorial_eq_sum k m)

/-- **Lee's alternating expansion of Stirling numbers of the second kind.** Write $S(n, k)$ for
the Stirling number of the second kind, the number of partitions of an $n$-element set into $k$
nonempty blocks. For natural numbers $m \le n$, the following identity of integers holds:
$$S(n, m) = \sum_{k=m}^{n} (-1)^{k-m} \binom{n}{k}\, m^{n-k}\, S(k, m).$$

Source: Kwankyu Lee, "Some New Identities for Stirling Numbers", Theorem 2
(TeX label `thm:kscasc`). -/
public theorem stirlingSecond_eq_sum_choose_pow {m n : ℕ} (hmn : m ≤ n) :
    (Nat.stirlingSecond n m : ℤ) =
      ∑ k ∈ Finset.Icc m n,
        (Nat.choose n k : ℤ) * (Nat.stirlingSecond k m : ℤ) *
          (m : ℤ) ^ (n - k) * (-1 : ℤ) ^ (k - m) := by
  apply mul_left_cancel₀ (show (m.factorial : ℤ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero m)
  let c (j : ℕ) : ℤ := (-1 : ℤ) ^ (m - j) * (Nat.choose m j : ℤ)
  let w (k : ℕ) : ℤ := (Nat.choose n k : ℤ) * (m : ℤ) ^ (n - k) * (-1 : ℤ) ^ k
  let f (k : ℕ) : ℤ := w k * ((m.factorial : ℤ) * (Nat.stirlingSecond k m : ℤ)) * (-1 : ℤ) ^ m
  symm
  calc
    _ = ∑ k ∈ Icc m n, f k := by
      rw [mul_sum]
      refine sum_congr rfl fun k hk ↦ ?_
      rw [neg_one_pow_sub_eq_mul (mem_Icc.mp hk).1]
      dsimp [f, w]
      ring
    _ = ∑ k ∈ range (n + 1), f k := by
      have hzero : ∑ k ∈ range m, f k = 0 := by
        refine sum_eq_zero fun k hk ↦ ?_
        simp [f, Nat.stirlingSecond_eq_zero_of_lt (mem_range.mp hk)]
      have hIco : Ico m (n + 1) = Icc m n := by
        ext k
        simp only [mem_Ico, mem_Icc, Nat.lt_succ_iff]
      simpa only [hzero, zero_add, hIco] using
        sum_range_add_sum_Ico f (Nat.le_succ_of_le hmn)
    _ = ∑ j ∈ range (m + 1), (c j * (-1 : ℤ) ^ m) * ((m : ℤ) - j) ^ n := by
      calc
        _ = ∑ k ∈ range (n + 1), ∑ j ∈ range (m + 1),
            (c j * (-1 : ℤ) ^ m) * ((-(j : ℤ)) ^ k * (m : ℤ) ^ (n - k) *
              (Nat.choose n k : ℤ)) := by
          refine sum_congr rfl fun k _ ↦ ?_
          dsimp [f]
          rw [factorial_mul_stirlingSecond_eq_sum, mul_sum, sum_mul]
          refine sum_congr rfl fun j _ ↦ ?_
          rw [neg_eq_neg_one_mul, mul_pow]
          dsimp [c, w]
          ring
        _ = _ := by
          rw [sum_comm]
          refine sum_congr rfl fun j _ ↦ ?_
          rw [← mul_sum, sub_eq_neg_add, add_pow]
    _ = _ := by
      rw [factorial_mul_stirlingSecond_eq_sum]
      change _ = ∑ j ∈ range (m + 1), c j * (j : ℤ) ^ n
      rw [← sum_range_reflect (fun j ↦ c j * (j : ℤ) ^ n) (m + 1)]
      refine sum_congr rfl fun j hj ↦ ?_
      have hjm : j ≤ m := Nat.le_of_lt_succ (mem_range.mp hj)
      rw [show m + 1 - 1 - j = m - j by omega, Nat.cast_sub hjm]
      dsimp [c]
      rw [Nat.choose_symm hjm, Nat.sub_sub_self hjm, neg_one_pow_sub_eq_mul hjm]
      calc
        _ = (-1 : ℤ) ^ m * (-1 : ℤ) ^ m *
            ((-1 : ℤ) ^ j * (Nat.choose m j : ℤ) * ((m : ℤ) - j) ^ n) := by ring
        _ = _ := by rw [← mul_pow]; simp

end MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted
