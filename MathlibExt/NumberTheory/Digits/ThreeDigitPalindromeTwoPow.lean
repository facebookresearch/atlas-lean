/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.List.Palindrome
public import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Linarith

/-!
# The criterion for three-digit palindromic powers of two

For a three-digit number, the first and last digits are its remainder upon division by the base
and the quotient upon division by the base twice. The two rational inequalities in the criterion
say that this second quotient is the remainder.
-/

namespace MetaMathlibExt

private theorem digits_eq_three {N b : ℕ} (hb : 1 < b) (hlo : b ^ 2 ≤ N)
    (hhi : N < b ^ 3) : Nat.digits b N = [N % b, (N / b) % b, N / b / b] := by
  have hb0 : 0 < b := by omega
  have hN : 0 < N := (pow_pos hb0 2).trans_le hlo
  have hq : b ≤ N / b := (Nat.le_div_iff_mul_le hb0).2 (by simpa [pow_two] using hlo)
  have ht : 1 ≤ N / b / b := (Nat.le_div_iff_mul_le hb0).2 (by simpa using hq)
  have hq' : N / b / b < b := (Nat.div_lt_iff_lt_mul hb0).2
    ((Nat.div_lt_iff_lt_mul hb0).2 (by simpa [pow_succ] using hhi))
  rw [Nat.digits_eq_cons_digits_div hb hN.ne',
    Nat.digits_eq_cons_digits_div hb (by omega : N / b ≠ 0),
    Nat.digits_of_lt b (N / b / b) (by omega) hq']

private theorem div_eq_iff_digit_bounds {q b c : ℕ} (hb : 0 < b) :
    q / b = c ↔ ((q : ℚ) / b - ((b : ℚ) - 1) / b ≤ (c : ℚ)) ∧
      ((c : ℚ) ≤ (q : ℚ) / b) := by
  have hbQ : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have hlo : ((q : ℚ) / b - ((b : ℚ) - 1) / b ≤ (c : ℚ)) ↔
      q + 1 ≤ (c + 1) * b := by
    rw [← sub_div, div_le_iff₀ hbQ]
    have h : ((q : ℚ) - ((b : ℚ) - 1) ≤ (c : ℚ) * b) ↔
        (q : ℚ) + 1 ≤ ((c : ℚ) + 1) * b := by
      rw [add_mul, one_mul]
      constructor <;> intro h <;> linarith
    rw [h]
    norm_cast
  have hhi : ((c : ℚ) ≤ (q : ℚ) / b) ↔ c * b ≤ q := by
    rw [le_div_iff₀ hbQ]
    norm_cast
  rw [hlo, hhi, ← Nat.lt_iff_add_one_le, ← Nat.div_lt_iff_lt_mul hb,
    ← Nat.le_div_iff_mul_le hb]
  omega

/-- **Three-digit palindromic powers of two.** Let $n$ be a natural number, let $b \ge 2$ be a
base, and let $c = 2^n \bmod b$. The base-$b$ representation of $2^n$ is a palindrome with exactly
three digits if and only if $b^2 + 1 \le 2^n \le b^3 - 1$, $c \ne 0$, and
$\frac{1}{b} \lfloor 2^n / b \rfloor - \frac{b - 1}{b} \le c \le
\frac{1}{b} \lfloor 2^n / b \rfloor$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 2
(`integers-2024-A69-thm-2`). -/
public theorem three_digit_palindrome_two_pow_iff (n b : ℕ) (hb : 2 ≤ b) :
    ((Nat.digits b (2 ^ n)).Palindrome ∧ (Nat.digits b (2 ^ n)).length = 3) ↔
      b ^ 2 + 1 ≤ 2 ^ n ∧ 2 ^ n ≤ b ^ 3 - 1 ∧ 2 ^ n % b ≠ 0 ∧
        ((2 ^ n / b : ℕ) : ℚ) / b - ((b : ℚ) - 1) / b ≤ ((2 ^ n % b : ℕ) : ℚ) ∧
        ((2 ^ n % b : ℕ) : ℚ) ≤ ((2 ^ n / b : ℕ) : ℚ) / b := by
  let N : ℕ := 2 ^ n
  change ((Nat.digits b N).Palindrome ∧ (Nat.digits b N).length = 3) ↔
    b ^ 2 + 1 ≤ N ∧ N ≤ b ^ 3 - 1 ∧ N % b ≠ 0 ∧
      ((N / b : ℕ) : ℚ) / b - ((b : ℚ) - 1) / b ≤ ((N % b : ℕ) : ℚ) ∧
      ((N % b : ℕ) : ℚ) ≤ ((N / b : ℕ) : ℚ) / b
  have hb' : 1 < b := by omega
  have hb0 : 0 < b := by omega
  constructor
  · rintro ⟨hpal, hlen⟩
    have hlo : b ^ 2 ≤ N := (Nat.lt_digits_length_iff hb' N).mp (by omega)
    have hhi : N < b ^ 3 := (Nat.digits_length_le_iff hb' N).mp (by omega)
    have hd := digits_eq_three hb' hlo hhi
    have heq : N / b / b = N % b := by
      have hr := hpal.reverse_eq
      rw [hd] at hr
      exact List.head_eq_of_cons_eq hr
    have hq : b ≤ N / b := (Nat.le_div_iff_mul_le hb0).2 (by simpa [pow_two] using hlo)
    have ht : 1 ≤ N / b / b := (Nat.le_div_iff_mul_le hb0).2 (by simpa using hq)
    have hc : N % b ≠ 0 := by omega
    have hne : N ≠ b ^ 2 := by
      intro h
      apply hc
      simp [h, pow_two]
    exact ⟨by omega, by omega, hc, (div_eq_iff_digit_bounds hb0).mp heq⟩
  · rintro ⟨hlo, hhi, _, hl, hu⟩
    have hb3 : 0 < b ^ 3 := pow_pos hb0 3
    have hd := digits_eq_three hb' (by omega : b ^ 2 ≤ N) (by omega : N < b ^ 3)
    have heq : N / b / b = N % b := (div_eq_iff_digit_bounds hb0).mpr ⟨hl, hu⟩
    rw [hd, heq]
    exact ⟨List.Palindrome.cons_concat _ (List.Palindrome.singleton _), rfl⟩

end MetaMathlibExt
