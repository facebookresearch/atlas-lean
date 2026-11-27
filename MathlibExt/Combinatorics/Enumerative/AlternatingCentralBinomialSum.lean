/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Ring.CharZero
import MathlibExt.Combinatorics.Enumerative.CentralBinomialBernstein

/-!
# Alternating sum of central binomial coefficients

At `x = -1` the powers of two in the Bernstein identity cancel. Choosing two disjoint
sets of size `k` in succession gives the two binomial factors on the right.
-/

namespace MetaMathlibExt

open Finset

/-- **Alternating sum of $\binom{n}{k} \binom{2k}{k}$.** For every natural number $n$,
$$\sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} \binom{2k}{k}
= \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{k} \binom{n-k}{k}$$
as integers.

Both sides are the central trinomial coefficient.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 6 (`integers-2026-A19-prop-6`). -/
public theorem sum_neg_one_pow_sub_choose_centralBinom (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * ((2 * k).choose k : ℤ) =
      ∑ k ∈ range (n / 2 + 1), (n.choose k : ℤ) * ((n - k).choose k : ℤ) := by
  have cancel (a b : ℂ) (m : ℕ) : a / 2 ^ m * b * 2 ^ m = a * b := by
    rw [mul_right_comm, div_mul_cancel₀ _ (pow_ne_zero m two_ne_zero)]
  have choose (k : ℕ) :
      (n.choose (2 * k) : ℂ) * (2 * k).choose k = (n.choose k : ℂ) * (n - k).choose k := by
    norm_cast
    simpa [two_mul] using Nat.choose_mul (n := n) (k := k + k) (s := k) (by omega)
  have h := sum_choose_centralBinom_one_sub_pow_mul_pow n (-1)
  simp only [sub_neg_eq_add, one_add_one_eq_two, cancel, choose] at h
  apply Int.cast_injective (α := ℂ)
  push_cast
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

open Polynomial in
/-- **Knuth's old sum (the Reed–Dawson identity).** For every natural number $n$, the sum
$\sum_{k=0}^{n} (-1)^k \binom{n}{k} \binom{2k}{k} 2^{-k}$ equals $2^{-n} \binom{n}{n/2}$ if $n$
is even and $0$ if $n$ is odd.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 1 (`integers-2026-A19-thm-1`). -/
public theorem knuth_old_sum (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) * ((2 * k).choose k : ℚ) / 2 ^ k =
      if Even n then (n.choose (n / 2) : ℚ) / 2 ^ n else 0 := by
  have hhalf : C (1 / 2 : ℚ) + C (1 / 2 : ℚ) = (1 : ℚ[X]) := by
    rw [← map_add, show (1 / 2 : ℚ) + 1 / 2 = 1 by norm_num, map_one]
  have hpoly : C (-1 / 2 : ℚ) * (1 + X) ^ 2 + X = C (-1 / 2 : ℚ) * (1 + X ^ 2) := by
    simp only [neg_div, map_neg]
    calc
      _ = -C (1 / 2 : ℚ) * (1 + X ^ 2) + X * (1 - (C (1 / 2 : ℚ) + C (1 / 2 : ℚ))) := by
        ring
      _ = _ := by rw [hhalf, sub_self, mul_zero, add_zero]
  -- Compute the middle coefficient first by expanding the sum and then using only even powers.
  calc
    _ = ((C (-1 / 2 : ℚ) * (1 + X) ^ 2 + X) ^ n).coeff n := by
      rw [add_pow, finsetSum_coeff]
      refine sum_congr rfl fun k hk ↦ ?_
      have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
      rw [mul_pow, ← map_pow, ← pow_mul, coeff_mul_natCast, mul_assoc (C _), coeff_C_mul,
        coeff_mul_X_pow']
      simp only [Nat.sub_le, ite_true, Nat.sub_sub_self hkn, coeff_one_add_X_pow]
      rw [div_pow]
      ring
    _ = _ := by
      rw [hpoly, mul_pow, ← map_pow, coeff_C_mul]
      have hexpand : expand ℚ 2 ((1 + X) ^ n) = (1 + X ^ 2) ^ n := by
        rw [map_pow, map_add, map_one, expand_X]
      rw [← hexpand, coeff_expand (by decide), coeff_one_add_X_pow]
      simp only [← even_iff_two_dvd]
      by_cases hn : Even n
      · simp only [ite_eq_left hn]
        rw [div_pow, hn.neg_one_pow, one_div, div_eq_mul_inv, mul_comm]
      · simp only [ite_eq_right hn, mul_zero]

end MetaMathlibExt
