/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPolynomial

/-!
# Rescaling a weighted binomial polynomial

The Bernstein form follows from the alternating form by substituting the inverse of `1 - x`
and clearing its powers. At `x = 1` only the zeroth term of each sum survives.

## References

* Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related Sums*,
  INTEGERS 26 (2026), Article A19, pp. 1–24, Corollary 6, equation (53) (p. 18).
  The proof here uses Corollary 4, equation (45) (p. 16), rather than specializing Theorem 15.
* In the paper's integral approach, Lemma 1 credits the beta integral to I. S. Gradshteyn and
  I. M. Ryzhik, *Table of Integrals, Series, and Products*, 7th ed., Elsevier Academic Press
  (2007), entry 3.621.5.
-/

namespace MetaMathlibExt

open Finset

/-- **Polynomial identity in $x$ and $1 - x$ with weights $2^k/(k+1)$.** For every natural
number $n$ and every complex number $x$,
$$
\sum_{k=0}^{n} \binom{n}{k} \frac{2^k}{k+1} (1-x)^k x^{n-k}
= \sum_{k=0}^{\lfloor n/2 \rfloor} \frac{1}{2k+1} \binom{n}{2k} (1-x)^{2k}.
$$

This is equation (53) of the source.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 6 (`integers-2026-A19-cor-6`). -/
public theorem sum_choose_two_pow_div_succ_one_sub_pow_mul_pow (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℂ) * 2 ^ k / (k + 1) * (1 - x) ^ k * x ^ (n - k) =
      ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℂ) / (2 * k + 1) * (1 - x) ^ (2 * k) := by
  by_cases hx : x = 1
  · subst x
    simp only [sub_self, one_pow, mul_one]
    calc
      _ = (1 : ℂ) := by
        rw [sum_eq_single 0]
        · simp
        · intro k _ hk
          simp [zero_pow hk]
        · simp
      _ = _ := by
        symm
        rw [sum_eq_single 0]
        · simp
        · intro k _ hk
          simp [zero_pow (show 2 * k ≠ 0 by omega)]
        · simp
  · have hne : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have hbase : (-1 : ℂ) * (1 - (1 - x)⁻¹) = x * (1 - x)⁻¹ := by
      field_simp [hne]
      ring
    have cancel (j : ℕ) (hj : j ≤ n) : (1 - x)⁻¹ ^ (n - j) * (1 - x) ^ n = (1 - x) ^ j := by
      calc
        _ = ((1 - x)⁻¹ ^ (n - j) * (1 - x) ^ (n - j)) * (1 - x) ^ j := by
          rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hj]
        _ = _ := by rw [← mul_pow, inv_mul_cancel₀ hne, one_pow, one_mul]
    have h := congrArg (· * (1 - x) ^ n) (sum_choose_two_pow_div_succ_one_sub_pow n (1 - x)⁻¹)
    simp only [sum_mul] at h
    convert h using 1
    · refine sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      calc
        _ = (n.choose k : ℂ) * 2 ^ k / (k + 1) *
            (x ^ (n - k) * ((1 - x)⁻¹ ^ (n - k) * (1 - x) ^ n)) := by
          rw [cancel k hk']
          ring
        _ = _ := by
          rw [← mul_assoc (x ^ (n - k)), ← mul_pow, ← hbase, mul_pow]
          ring
    · refine sum_congr rfl fun k hk => ?_
      have hk' : 2 * k ≤ n := by
        have := mem_range.mp hk
        omega
      rw [mul_assoc, cancel (2 * k) hk']

end MetaMathlibExt
