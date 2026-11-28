/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Nat.Digits.Defs
import MathlibExt.NumberTheory.Digits.ThreeDigitBinomialForm

/-!
# Three-digit representations of powers of two with outer digits one

The theorem `one_c_one_two_pow_iff` characterizes the digits `[1, c, 1]` with `c ≠ 2` by
factoring `2 ^ n - 1` and excluding the binomial representation `[1, 2, 1]`.
-/

namespace MetaMathlibExt

/-- **Three-digit representations of powers of two with outer digits one.** Let $n$ be a natural
number and $b \ge 2$ a base. There is a digit $c \ne 2$ such that the base-$b$ representation of
$2^n$ is $(1, c, 1)_b$, that is, $2^n = 1 + cb + b^2$ with $0 \le c < b$, if and only if
(i) $2^n - 1 = kb$ for some natural number $k$ with $b \le k \le 2b - 1$, and (ii) it is not the
case that $n$ is even and $b = 2^{n/2} - 1$.

The excluded digit $c = 2$ gives the binomial form $(1, 2, 1)_b = (b + 1)^2$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 4
(`integers-2024-A69-thm-4`). -/
public theorem one_c_one_two_pow_iff (n b : ℕ) (hb : 2 ≤ b) :
    (∃ c, c ≠ 2 ∧ Nat.digits b (2 ^ n) = [1, c, 1]) ↔
      (∃ k, 2 ^ n - 1 = k * b ∧ b ≤ k ∧ k ≤ 2 * b - 1) ∧ ¬ (Even n ∧ b = 2 ^ (n / 2) - 1) := by
  have binomial : Nat.digits b (2 ^ n) = [1, 2, 1] ↔ Even n ∧ b = 2 ^ (n / 2) - 1 := by
    have h : Nat.digits b (2 ^ n) = [1, 2, 1] ↔
        2 < n ∧ n % 2 = 0 ∧ b = 2 ^ (n / 2) - 1 := by
      simpa [eq_comm (a := 1)] using three_digit_binomialForm_two_pow_iff n b 1 hb (by decide)
    rw [h, Nat.even_iff]
    apply and_iff_right_of_imp
    rintro ⟨_, hbase⟩
    have hpow : (2 : ℕ) ^ 1 < 2 ^ (n / 2) := by omega
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 hpow
    omega
  have value (c : ℕ) : Nat.ofDigits b [1, c, 1] = 1 + (b + c) * b := by
    simp [Nat.ofDigits, Nat.mul_comm, Nat.add_comm]
  constructor
  · rintro ⟨c, hc, hd⟩
    have hlt : c < b := Nat.digits_lt_base (m := 2 ^ n) hb (by simp [hd])
    have hval := congrArg (Nat.ofDigits b) hd
    rw [Nat.ofDigits_digits, value] at hval
    refine ⟨⟨b + c, by omega, by omega, by omega⟩, ?_⟩
    intro h
    exact hc (by simpa using hd.symm.trans (binomial.2 h))
  · rintro ⟨⟨k, hk, hlow, hhigh⟩, hexcl⟩
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hlow
    have hc : c < b := by omega
    have hval : 2 ^ n = Nat.ofDigits b [1, c, 1] := by
      rw [value]
      have := Nat.two_pow_pos n
      omega
    have hd : Nat.digits b (2 ^ n) = [1, c, 1] := by
      rw [hval]
      apply Nat.digits_ofDigits b hb
      · simp [show 1 < b from hb, hc]
      · simp
    exact ⟨c, fun h => hexcl (binomial.1 (h ▸ hd)), hd⟩

end MetaMathlibExt
