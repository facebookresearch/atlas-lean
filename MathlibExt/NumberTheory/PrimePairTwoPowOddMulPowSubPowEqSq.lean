/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Squares of the form `(2 ^ (2 * k + 1) * (2 * p - 1)) ^ x - p ^ y` for prime pairs

Let `p ≡ 5 (mod 8)`, so that `p ^ y ≡ 1 (mod 4)`. The `x`-th power of the base
`2 ^ (2 * k + 1) * (2 * p - 1)` is divisible by `2 ^ ((2 * k + 1) * x)`. If
`(2 * k + 1) * x ≥ 2`, reduction modulo four therefore gives `z ^ 2 ≡ -1`, which is impossible.
So a solution with `x ≥ 1` has `k = 0` and `x = 1`, and the equation reads
`4 * p - 2 - p ^ y = z ^ 2`. For `y = 0` this is `4 * p = z ^ 2 + 3`. For `y = 1` the left side
`3 * p - 2` is `5` modulo eight, which is not a square modulo eight. For `y ≥ 2` the left side is
negative, since `p ^ y ≥ p ^ 2 ≥ 5 * p`. With `x = 0` the left side `1 - p ^ y` is negative unless
`y = 0`, and then `z = 0`.

The argument uses only the congruence `p ≡ 5 (mod 8)`: it needs neither `p` nor `2 * p - 1` to be
prime.
-/

namespace MetaMathlibExt

namespace prime_pair_two_pow_odd_mul_pow_sub_pow_eq_sq_iff

/-- For `p ≡ 5 (mod 8)` and `x ≥ 1`, the equation
`(2 ^ (2 * k + 1) * (2 * p - 1)) ^ x - p ^ y = z ^ 2` forces `k = 0` and `x = 1`: otherwise the
power is divisible by four and the equation exhibits `-1` as a square modulo four. -/
private theorem k_eq_zero_and_x_eq_one {p k x y z : ℕ} (hp8 : p % 8 = 5) (hx : x ≠ 0)
    (h : ((2 : ℤ) ^ (2 * k + 1) * (2 * p - 1)) ^ x - (p : ℤ) ^ y = (z : ℤ) ^ 2) :
    k = 0 ∧ x = 1 := by
  by_contra hkx
  have hexp : 2 ≤ (2 * k + 1) * x := by
    obtain _ | _ | x := x
    · exact absurd rfl hx
    · have hk : k ≠ 0 := fun hk => hkx ⟨hk, rfl⟩
      omega
    · nlinarith
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hexp
  have hp : (p : ZMod 4) = 1 := (ZMod.natCast_eq_natCast_iff' p 1 4).mpr (by omega)
  have hpow : ((2 : ZMod 4) ^ (2 * k + 1) * (2 * 1 - 1)) ^ x = 0 := by
    rw [show (2 * 1 - 1 : ZMod 4) = 1 by decide, mul_one, ← pow_mul, hm, pow_add,
      show (2 : ZMod 4) ^ 2 = 0 by decide, mul_zero]
  have hmod := congrArg (Int.cast : ℤ → ZMod 4) h
  push_cast at hmod
  rw [hp, hpow, one_pow, zero_sub] at hmod
  exact (by decide : ∀ a : ZMod 4, -1 ≠ a ^ 2) z hmod

end prime_pair_two_pow_odd_mul_pow_sub_pow_eq_sq_iff

open prime_pair_two_pow_odd_mul_pow_sub_pow_eq_sq_iff

set_option linter.unusedVariables false in
/-- **Squares of the form $(2^{2k+1}(2p - 1))^x - p^y$ for prime pairs.** Let $p$ be a prime with
$p \equiv 5 \pmod 8$ such that $2p - 1$ is prime, and let $k$ be a non-negative integer. Then
non-negative integers $x$, $y$ and $z$ satisfy $(2^{2k+1}(2p - 1))^x - p^y = z^2$ if and only if
$(x, y, z) = (0, 0, 0)$, or $k = 0$, $x = 1$, $y = 0$ and $4p = z^2 + 3$.

In the last case the two primes are $p = (z^2 + 3)/4$ and $2p - 1 = (z^2 + 1)/2$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 7. -/
public theorem prime_pair_two_pow_odd_mul_pow_sub_pow_eq_sq_iff {p : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp8 : p % 8 = 5) (k x y z : ℕ) :
    ((2 : ℤ) ^ (2 * k + 1) * (2 * p - 1)) ^ x - (p : ℤ) ^ y = (z : ℤ) ^ 2 ↔
      (x, y, z) = (0, 0, 0) ∨ (4 * p = z ^ 2 + 3 ∧ k = 0 ∧ x = 1 ∧ y = 0) := by
  have hp5 : (5 : ℤ) ≤ p := by exact_mod_cast (show 5 ≤ p by omega)
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · left
      rw [pow_zero] at h
      obtain rfl : y = 0 := by
        by_contra hy
        have := one_lt_pow₀ (show (1 : ℤ) < p by linarith) hy
        linarith [sq_nonneg (z : ℤ)]
      simp only [pow_zero, sub_self] at h
      obtain rfl : z = 0 := by exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h.symm
      rfl
    · obtain ⟨rfl, rfl⟩ := k_eq_zero_and_x_eq_one hp8 hx.ne' h
      have h' : 4 * (p : ℤ) - 2 - (p : ℤ) ^ y = (z : ℤ) ^ 2 := by linear_combination h
      right
      obtain _ | _ | y := y
      · refine ⟨?_, rfl, rfl, rfl⟩
        have h4 : 4 * (p : ℤ) = (z : ℤ) ^ 2 + 3 := by linear_combination h'
        exact_mod_cast h4
      · exfalso
        have h3 : 3 * (p : ℤ) - 2 = (z : ℤ) ^ 2 := by linear_combination h'
        have hp' : (p : ZMod 8) = 5 := (ZMod.natCast_eq_natCast_iff' p 5 8).mpr (by omega)
        have hmod := congrArg (Int.cast : ℤ → ZMod 8) h3
        push_cast at hmod
        rw [hp'] at hmod
        exact (by decide : ∀ a : ZMod 8, 3 * 5 - 2 ≠ a ^ 2) z hmod
      · exfalso
        have hpow : (p : ℤ) ^ 2 ≤ (p : ℤ) ^ (y + 1 + 1) :=
          pow_le_pow_right₀ (by linarith) (by omega)
        nlinarith [sq_nonneg (z : ℤ)]
  · rintro (h | ⟨h, rfl, rfl, rfl⟩)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp
    · have h4 : 4 * (p : ℤ) = (z : ℤ) ^ 2 + 3 := by exact_mod_cast h
      linear_combination h4

end MetaMathlibExt
