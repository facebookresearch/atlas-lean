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

/-- Prepending a bit `b < 2` to the binary expansion of `m` adds `b` to its digit sum. -/
private theorem hammingWeight_add_two_mul {b : ℕ} (hb : b < 2) (m : ℕ) :
    (Nat.digits 2 (b + 2 * m)).sum = b + (Nat.digits 2 m).sum := by
  by_cases h : b = 0 ∧ m = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [Nat.digits_add 2 one_lt_two b m hb (not_and_or.mp h), List.sum_cons]

/-- **Hamming weight of the successor of an even number.** For a natural number $m$, write
$s_1(m)$ for the sum of the binary digits of $m$ (the number of ones in its binary expansion).
If $n$ is an even natural number (including $n = 0$), then $s_1(n + 1) = s_1(n) + 1$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 14 (`jis-2024-24.2.7-lem-14`). -/
public theorem hammingWeight_succ_of_even (n : ℕ) (hn : Even n) :
    (Nat.digits 2 (n + 1)).sum = (Nat.digits 2 n).sum + 1 := by
  obtain ⟨m, rfl⟩ := hn
  -- Write `m + m + 1` and `m + m` as the bits `1` and `0` below `m`.
  rw [show m + m + 1 = 1 + 2 * m by omega, show m + m = 0 + 2 * m by omega,
    hammingWeight_add_two_mul one_lt_two, hammingWeight_add_two_mul two_pos]
  omega

/-- **Hamming weight of the predecessor of an odd number.** For a natural number $m$, write
$s_1(m)$ for the sum of the binary digits of $m$ (the number of ones in its binary expansion).
If $n$ is an odd natural number, then $s_1(n - 1) = s_1(n) - 1$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 15 (`jis-2024-24.2.7-lem-15`). -/
public theorem hammingWeight_pred_of_odd (n : ℕ) (hn : Odd n) :
    (Nat.digits 2 (n - 1)).sum = (Nat.digits 2 n).sum - 1 := by
  obtain ⟨m, rfl⟩ := hn
  -- `n - 1 = 2 * m` is even, and `n` is its successor.
  rw [Nat.add_sub_cancel, hammingWeight_succ_of_even _ (even_two_mul m), Nat.add_sub_cancel]

/-- For `r < 2 ^ k`, the `k`-bit binary expansion of `2 ^ k - 1 - r` is that of `r` with every
bit flipped, so the two binary digit sums add up to `k`. -/
private theorem hammingWeight_two_pow_sub_one_sub_add (k : ℕ) {r : ℕ} (hr : r < 2 ^ k) :
    (Nat.digits 2 (2 ^ k - 1 - r)).sum + (Nat.digits 2 r).sum = k := by
  induction k generalizing r with
  | zero =>
    obtain rfl : r = 0 := by simpa using hr
    simp
  | succ k ih =>
    -- Split off the lowest bit `r % 2`: the complement has lowest bit `1 - r % 2`, and above it
    -- the complement `2 ^ k - 1 - r / 2` of `r / 2 < 2 ^ k`.
    rw [pow_succ] at hr ⊢
    rw [show 2 ^ k * 2 - 1 - r = (1 - r % 2) + 2 * (2 ^ k - 1 - r / 2) by omega,
      hammingWeight_add_two_mul (b := 1 - r % 2) (by omega)]
    have hlow := hammingWeight_add_two_mul (Nat.mod_lt r two_pos) (r / 2)
    rw [Nat.mod_add_div] at hlow
    have := ih (r := r / 2) (by omega)
    omega

/-- **Hamming weight of a power of two minus an odd number.** For a natural number $m$, write
$s_1(m)$ for the sum of the binary digits of $m$ (the number of ones in its binary expansion).
Let $k$ and $r$ be natural numbers with $r$ odd and $2r < 2^k$, that is, $r < 2^{k-1}$. Then
$s_1(2^k - r) = 1 + k - s_1(r)$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 16 (`jis-2024-24.2.7-lem-16`). -/
public theorem hammingWeight_two_pow_sub_of_odd (k r : ℕ) (hodd : Odd r)
    (hr : 2 * r < 2 ^ k) :
    (Nat.digits 2 (2 ^ k - r)).sum = 1 + k - (Nat.digits 2 r).sum := by
  -- `k = 0` would force `2 * r < 1`, so `r = 0`, which is not odd.
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hr
    obtain ⟨j, rfl⟩ := hodd
    omega
  -- So `2 ^ k - 1` is odd and `2 ^ k - 1 - r` is even, and `2 ^ k - r` is its successor.
  have heven : Even (2 ^ k - 1 - r) :=
    Nat.Odd.sub_odd (Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, hk⟩)
      odd_one) hodd
  have hcompl := hammingWeight_two_pow_sub_one_sub_add k (r := r) (by omega)
  rw [show 2 ^ k - r = 2 ^ k - 1 - r + 1 by omega, hammingWeight_succ_of_even _ heven]
  omega

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
