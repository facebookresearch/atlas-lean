/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Lemmas

/-! # Binary digit sums -/

namespace MetaMathlibExt

open Finset

/-- **Adding a larger power of two raises the Hamming weight by one.** For a natural number $m$,
write $s_1(m)$ for the sum of the binary digits of $m$ (the number of ones in its binary
expansion). For all natural numbers $k$ and $r$ with $r < 2^k$, $s_1(2^k + r) = s_1(r) + 1$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 13 (`jis-2024-24.2.7-lem-13`). -/
public theorem hammingWeight_two_pow_add (k r : ℕ) (hr : r < 2 ^ k) :
    (Nat.digits 2 (2 ^ k + r)).sum = (Nat.digits 2 r).sum + 1 := by
  obtain ⟨padding, rfl⟩ := Nat.exists_eq_add_of_le ((Nat.digits_length_le_iff one_lt_two r).2 hr)
  have hdigits := Nat.digits_append_zeroes_append_digits (n := r) (k := padding)
    one_lt_two Nat.zero_lt_one
  simpa [add_comm, Nat.digits_of_lt 2 1 one_ne_zero one_lt_two] using
    (congrArg List.sum hdigits).symm

/-- **Sum of binary digit sums below a power of two.** For a natural number $i$, let $s_1(i)$
denote the sum of the binary digits of $i$. Then for every natural number $m$,
$2 \sum_{i < 2^m} s_1(i) = 2^m m$; that is, the binary expansions of $0, 1, \dots, 2^m - 1$
contain $2^m m / 2$ ones in total.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 29 (`jis-2024-24.2.7-lem-29`). -/
public theorem two_mul_sum_hammingWeight_range_two_pow (m : ℕ) :
    2 * ∑ i ∈ range (2 ^ m), (Nat.digits 2 i).sum = 2 ^ m * m := by
  rw [Nat.sum_sum_digits_eq (b := 2) (by decide), Nat.choose_self, mul_one]
  cases m with
  | zero => simp
  | succ m => simp [pow_succ, mul_comm, mul_left_comm]

end MetaMathlibExt
