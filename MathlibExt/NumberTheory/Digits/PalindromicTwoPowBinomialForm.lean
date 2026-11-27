/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Palindrome
public import MathlibExt.NumberTheory.Digits.BinomialDigits
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Binomial forms of palindromic powers of two

In base `2 ^ x - 1`, the first and last digits of a palindrome are equal and nonzero.
The integer is therefore strictly greater than the base raised to the index of its leading digit
when that index is positive. To recognize a binomial form, the two scaled coefficient bounds
follow from Pascal's recurrence starting in rows `1` and `3`, respectively.
-/

namespace MetaMathlibExt

private theorem choose_add_three_le (m i : ℕ) : (m + 3).choose i ≤ 3 * 2 ^ m := by
  induction m generalizing i with
  | zero => exact (Nat.choose_le_middle i 3).trans (by decide)
  | succ m ih =>
    rw [show m.succ + 3 = (m + 3) + 1 by omega]
    cases i with
    | zero =>
      rw [Nat.choose_zero_right, pow_succ]
      have hm := Nat.two_pow_pos m
      omega
    | succ i =>
      rw [Nat.choose_succ_succ', pow_succ]
      have h₀ := ih i
      have h₁ := ih (i + 1)
      omega

/-- **Palindromic powers of two in a base one less than a power of two.** Let $x \ge 2$ and
$n \ge 1$ be natural numbers, let $b = 2^x - 1$, and suppose that the base-$b$ representation
$2^n = (c_k, \dots, c_0)_b$ is a palindrome with $k + 1$ digits. Then (1) $n > k(x - 1)$; and
(2) if $n = kx + r$ for a natural number $r$, and either $k \le x - r$, or $3 \le k \le x - r + 1$
and $x \ge 3$, then $c_i = 2^r \binom{k}{i}$ for $i = 0, \dots, k$, that is, the representation
is the binomial form $2^r (\binom{k}{k}, \dots, \binom{k}{0})_b$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Lemma 4
(`integers-2024-A69-lem-4`). -/
public theorem palindrome_two_pow_base_two_pow_sub_one (x n k : ℕ) (hx : 2 ≤ x)
    (hn : 1 ≤ n) (hp : (Nat.digits (2 ^ x - 1) (2 ^ n)).Palindrome)
    (hk : (Nat.digits (2 ^ x - 1) (2 ^ n)).length = k + 1) :
    k * (x - 1) < n ∧
      ∀ r : ℕ, n = k * x + r →
        ((k : ℤ) ≤ (x : ℤ) - r ∨ (3 ≤ k ∧ (k : ℤ) ≤ (x : ℤ) - r + 1 ∧ 3 ≤ x)) →
        Nat.digits (2 ^ x - 1) (2 ^ n) = (List.range (k + 1)).map fun i => 2 ^ r * k.choose i := by
  let b := 2 ^ x - 1
  change (Nat.digits b (2 ^ n)).Palindrome at hp
  change (Nat.digits b (2 ^ n)).length = k + 1 at hk
  have hbase : 1 + b = 2 ^ x := by
    dsimp [b]
    have hxpos := Nat.two_pow_pos x
    omega
  have hhalf : (2 : ℕ) ^ (x - 1) < b := by
    have hmin : (2 : ℕ) ≤ 2 ^ (x - 1) :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 1 ≤ x - 1 by omega)
    have hdouble : (2 : ℕ) ^ x = 2 ^ (x - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ x)]
    omega
  have hb : 1 < b := Nat.one_le_two_pow.trans_lt hhalf
  constructor
  · by_cases hk0 : k = 0
    · rw [hk0, zero_mul]
      exact hn
    have hN := (Nat.two_pow_pos n).ne'
    have hrem : (2 : ℕ) ^ n % b ≠ 0 := by
      have heq := List.head?_reverse (l := Nat.digits b (2 ^ n))
      rw [hp.reverse_eq, List.getLast?_eq_some_getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hN)]
        at heq
      conv_lhs at heq => rw [Nat.digits_eq_cons_digits_div hb hN, List.head?_cons]
      rw [Option.some.inj heq]
      exact Nat.getLast_digit_ne_zero b hN
    have hle : b ^ k ≤ (2 : ℕ) ^ n := (Nat.lt_digits_length_iff hb _).mp (by omega)
    have hlt : b ^ k < (2 : ℕ) ^ n := by
      refine lt_of_le_of_ne hle ?_
      intro heq
      exact hrem (Nat.dvd_iff_mod_eq_zero.mp (heq ▸ dvd_pow_self b hk0))
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    calc
      (2 : ℕ) ^ (k * (x - 1)) = (2 ^ (x - 1)) ^ k := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ b ^ k := Nat.pow_le_pow_left hhalf.le _
      _ < 2 ^ n := hlt
  · intro r hnr hr
    change Nat.digits b (2 ^ n) = _
    have hvalue : (2 : ℕ) ^ n = 2 ^ r * (1 + b) ^ k := by
      rw [hbase, ← pow_mul, ← pow_add, Nat.add_comm r, Nat.mul_comm x, ← hnr]
    rw [hvalue]
    apply digits_mul_one_add_pow _ _ _ (Nat.one_le_two_pow)
    by_cases hk0 : k = 0
    · subst k
      have hsingle : (2 : ℕ) ^ n < b := by
        simpa only [pow_one] using
          (Nat.digits_length_le_iff (k := 1) hb _).mp (by omega)
      have hnr' : n = r := by simpa using hnr
      simpa [← hnr'] using hsingle
    rcases hr with hr | ⟨h3k, hr, h3x⟩
    · have hrk : r + k ≤ x := by omega
      have hchoose : k.choose ((k + 1) / 2) ≤ 2 ^ (k - 1) := by
        have hk1 : 1 ≤ k := by omega
        simpa only [Nat.sub_add_cancel hk1] using
          Nat.choose_succ_le_two_pow (k - 1) ((k + 1) / 2)
      calc
        _ ≤ 2 ^ r * 2 ^ (k - 1) := Nat.mul_le_mul_left _ hchoose
        _ = 2 ^ (r + (k - 1)) := (pow_add ..).symm
        _ ≤ 2 ^ (x - 1) := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega)
        _ < b := hhalf
    · have hrk : r + k ≤ x + 1 := by omega
      have hchoose : k.choose ((k + 1) / 2) ≤ 3 * 2 ^ (k - 3) := by
        simpa only [Nat.sub_add_cancel h3k] using choose_add_three_le (k - 3) ((k + 1) / 2)
      calc
        _ ≤ 2 ^ r * (3 * 2 ^ (k - 3)) := Nat.mul_le_mul_left _ hchoose
        _ = 3 * 2 ^ (r + (k - 3)) := by rw [pow_add]; ac_rfl
        _ ≤ 3 * 2 ^ (x - 2) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega))
        _ < b := by
          have hmin : (2 : ℕ) ≤ 2 ^ (x - 2) :=
            Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 1 ≤ x - 2 by omega)
          have hquad : (2 : ℕ) ^ x = 2 ^ (x - 2) * 4 := by
            rw [← show (2 : ℕ) ^ 2 = 4 by decide, ← pow_add, Nat.sub_add_cancel hx]
          omega

end MetaMathlibExt
