/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

/-!
# Three-digit binomial forms of powers of two

The digits `[α, 2 * α, α]` have value `α * (b + 1) ^ 2` in base `b`.
When this value is a power of two, both factors `α` and `b + 1` are powers of two.
The bound on the middle digit determines which exponents occur.
-/

namespace MetaMathlibExt

/-- **Three-digit binomial forms of powers of two.** Let $n$ and $\alpha \ge 1$ be natural numbers
and let $b \ge 2$ be a base. The base-$b$ representation of $2^n$ is
$(\alpha, 2\alpha, \alpha)_b$ if and only if there is a natural number $i$ with $3i + 2 < n$,
$n \equiv i \pmod 2$, $\alpha = 2^i$ and $b = 2^{(n - i)/2} - 1$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 3
(`integers-2024-A69-thm-3`). -/
public theorem three_digit_binomialForm_two_pow_iff (n b α : ℕ) (hb : 2 ≤ b)
    (hα : 1 ≤ α) :
    Nat.digits b (2 ^ n) = [α, 2 * α, α] ↔
      ∃ i : ℕ, 3 * i + 2 < n ∧ n % 2 = i % 2 ∧ α = 2 ^ i ∧ b = 2 ^ ((n - i) / 2) - 1 := by
  have hvalue : Nat.ofDigits b [α, 2 * α, α] = α * (b + 1) ^ 2 := by
    rw [Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.ofDigits_singleton]
    ring
  constructor
  · intro hdigits
    have hpow : 2 ^ n = α * (b + 1) ^ 2 := by
      rw [← Nat.ofDigits_digits b (2 ^ n), hdigits, hvalue]
    have hmiddle : 2 * α < b := Nat.digits_lt_base (m := 2 ^ n) hb (by simp [hdigits])
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show α ∣ 2 ^ n from ⟨_, hpow⟩)
    obtain ⟨x, _, hx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show b + 1 ∣ 2 ^ n from ⟨α * (b + 1), by rw [hpow]; ring⟩)
    have hn : n = i + x * 2 := Nat.pow_right_injective (by decide : 2 ≤ 2) (calc
      2 ^ n = α * (b + 1) ^ 2 := hpow
      _ = 2 ^ (i + x * 2) := by rw [pow_add, pow_mul, ← hi, ← hx])
    have hix : i + 1 < x := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (by
      rw [pow_succ, ← hi, ← hx]
      omega)
    refine ⟨i, by omega, by omega, hi, ?_⟩
    rw [show (n - i) / 2 = x by omega, ← hx, Nat.add_sub_cancel]
  · rintro ⟨i, hbound, hparity, hi, hbform⟩
    let x := (n - i) / 2
    have hn : n = i + x * 2 := by dsimp [x]; omega
    have hgap : i + 2 ≤ x := by omega
    have hbase : b + 1 = 2 ^ x := by
      have hpos : 0 < 2 ^ x := pow_pos (by decide) _
      change b = 2 ^ x - 1 at hbform
      omega
    have hmiddle : 2 * α < b := by
      have hle := Nat.pow_le_pow_right (by decide : 0 < 2) hgap
      rw [pow_succ, pow_succ, ← hi, ← hbase] at hle
      omega
    have hpow : 2 ^ n = Nat.ofDigits b [α, 2 * α, α] := by
      rw [hvalue, hn, pow_add, pow_mul, hi, hbase]
    rw [hpow]
    apply Nat.digits_ofDigits b hb
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      omega
    · intro h
      change α ≠ 0
      omega

end MetaMathlibExt
