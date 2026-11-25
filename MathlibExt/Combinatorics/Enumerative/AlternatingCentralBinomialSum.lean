/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
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

end MetaMathlibExt
