/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Order.Interval.Finset.Nat
import MathlibExt.Combinatorics.Enumerative.StirlingAscPochhammer

/-!
# Lee's expansion of shifted Stirling numbers of the first kind

Comparing coefficients in the rising factorial at `X + 1` and the falling factorial
at `X + n` expresses the shifted Stirling number as a signed binomial sum.
-/

open Finset Polynomial

namespace MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

/-- Expand the product of `X + 1` through `X + n` in powers of `X + n`. -/
private theorem ascPochhammer_comp_X_add_one_eq_sum (n : ℕ) :
    (ascPochhammer ℤ n).comp (X + 1) =
      ∑ k ∈ range (n + 1), (Nat.stirlingFirst n k : ℤ[X]) *
        C ((-1 : ℤ) ^ (n - k)) * (X + C (n : ℤ)) ^ k := by
  let p : ℤ[X] := X + C (n : ℤ)
  calc
    _ = (descPochhammer ℤ[X] n).eval p := by
      rw [descPochhammer_eval_eq_ascPochhammer, show p - (n : ℤ[X]) + 1 = X + 1 by simp [p]]
      exact (ascPochhammer_eval₂ C n (X + 1 : ℤ[X])).symm
    _ = (-1) ^ n * (ascPochhammer ℤ[X] n).eval (-p) := by
      rw [ascPochhammer_eval_neg_eq_descPochhammer, ← mul_assoc, ← mul_pow]
      simp
    _ = _ := by
      rw [← Nat.sum_stirlingFirst_mul_pow, mul_sum]
      refine sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
      have hsign : (-1 : ℤ[X]) ^ n * (-1) ^ k = (-1) ^ (n - k) := by
        rw [← pow_add, show n + k = n - k + 2 * k by omega, pow_add, pow_mul]
        simp
      rw [neg_eq_neg_one_mul p, mul_pow, map_pow, map_neg, map_one, ← hsign]
      simp only [p, mul_assoc, mul_left_comm]

/-- **Lee's expansion of shifted Stirling numbers of the first kind.** Write $c(n, k)$ for the
unsigned Stirling number of the first kind, the number of permutations of $n$ elements with
exactly $k$ cycles. For natural numbers $m \le n$, the following identity of integers holds:
$$c(n + 1, m + 1) = \sum_{k=m}^{n} (-1)^{n-k} \binom{k}{m}\, n^{k-m}\, c(n, k).$$

Source: Kwankyu Lee, "Some New Identities for Stirling Numbers", Theorem 1
(TeX label `thm:cksdd`). -/
public theorem stirlingFirst_succ_eq_sum_choose_pow {m n : ℕ} (hmn : m ≤ n) :
    (Nat.stirlingFirst (n + 1) (m + 1) : ℤ) =
      ∑ k ∈ Finset.Icc m n,
        (Nat.stirlingFirst n k : ℤ) * (Nat.choose k m : ℤ) *
          (-1 : ℤ) ^ (n - k) * (n : ℤ) ^ (k - m) := by
  calc
    _ = (ascPochhammer ℤ (n + 1)).coeff (m + 1) := by
      rw [← Nat.sum_stirlingFirst_mul_X_pow, finsetSum_coeff]
      simp [coeff_X_pow, mul_ite, hmn]
    _ = ∑ k ∈ range (n + 1), (Nat.stirlingFirst n k : ℤ) * k.choose m *
          (-1 : ℤ) ^ (n - k) * (n : ℤ) ^ (k - m) := by
      rw [ascPochhammer_succ_left, coeff_X_mul, ascPochhammer_comp_X_add_one_eq_sum,
        finsetSum_coeff]
      refine sum_congr rfl fun k _ => ?_
      rw [← C_eq_natCast, ← C_mul, coeff_C_mul, coeff_X_add_C_pow]
      ring
    _ = _ := by
      symm
      apply sum_subset fun k hk => mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hk).2)
      intro k hk hki
      have hkm : k < m := by
        simpa [mem_Icc, Nat.le_of_lt_succ (mem_range.mp hk)] using hki
      simp [Nat.choose_eq_zero_of_lt hkm]

end MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted
