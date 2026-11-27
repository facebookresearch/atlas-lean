/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Ring.CharZero
import MathlibExt.Combinatorics.Enumerative.CentralBinomialBernstein
import Mathlib.Tactic.NormNum

/-!
# Alternating weighted sum of central binomial coefficients

At `x = 2` in the Bernstein identity, the factor `(1 - x)^k` supplies the alternating sign;
on the even-index side it is `1`.
-/

namespace MetaMathlibExt

open Finset

/-- **Alternating sum of $\binom{n}{k} 2^{n-2k} \binom{2k}{k}$.** For every natural number $n$,
the following identity holds in $\mathbb{Q}$:
$$\sum_{k=0}^{n} (-1)^k \binom{n}{k} \frac{2^n}{2^{2k}} \binom{2k}{k}
= \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{2k} \frac{1}{2^{2k}} \binom{2k}{k}.$$

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 3 (`integers-2026-A19-prop-3`). -/
public theorem sum_neg_one_pow_choose_two_pow_centralBinom (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) * 2 ^ n / 2 ^ (2 * k) *
        ((2 * k).choose k : ℚ) =
      ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) / 2 ^ (2 * k) * ((2 * k).choose k : ℚ) := by
  apply (Rat.cast_injective (α := ℂ))
  change (Rat.castHom ℂ) _ = (Rat.castHom ℂ) _
  simp only [map_sum, map_mul, map_div₀, map_pow, map_natCast, map_ofNat, map_neg, map_one]
  have hsub : 1 - (2 : ℂ) = -1 := by norm_num
  have heven (k : ℕ) : (-1 : ℂ) ^ (2 * k) = 1 := by
    rw [pow_mul, neg_one_sq, one_pow]
  have h := sum_choose_centralBinom_one_sub_pow_mul_pow n 2
  simp only [hsub, heven, mul_one] at h
  refine Eq.trans ?_ h
  apply sum_congr rfl
  intro k hk
  have hkn := Nat.le_of_lt_succ (mem_range.mp hk)
  have hn : (2 : ℂ) ^ n = 2 ^ (n - k) * 2 ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkn]
  have hpow : (2 : ℂ) ^ n / 2 ^ (2 * k) = 2 ^ (n - k) / 2 ^ k := by
    rw [hn, two_mul, pow_add, mul_div_mul_right _ _ (pow_ne_zero k (two_ne_zero : (2 : ℂ) ≠ 0))]
  rw [mul_div_assoc, hpow]
  simp only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

end MetaMathlibExt
