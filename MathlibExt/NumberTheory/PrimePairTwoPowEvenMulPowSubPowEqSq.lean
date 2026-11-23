/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Squares of the form `(2 ^ (2 * k) * (2 * p - 1)) ^ x - p ^ y` for prime pairs

For positive `x`, reduction modulo four forces `y` to be odd. Modulo `q = 2 * p - 1`,
we then have `z ^ 2 = -p ^ y` and `2 * p = 1`. Multiplying by `2 ^ (y + 1)` would
make `-2` a square modulo `q`, whereas `q ≡ 5` modulo eight.
-/

namespace MetaMathlibExt

namespace prime_pair_two_pow_even_mul_pow_sub_pow_eq_sq_iff

private theorem odd_exponent_mod_four {p k x y z : ℕ} (hp4 : p % 4 = 3) (hk : 1 ≤ k)
    (hx : x ≠ 0) (h : ((2 : ℤ) ^ (2 * k) * (2 * p - 1)) ^ x - (p : ℤ) ^ y = (z : ℤ) ^ 2) :
    Odd y := by
  refine (Nat.even_or_odd y).resolve_left fun hy => ?_
  have hp : (p : ZMod 4) = -1 :=
    (ZMod.natCast_eq_natCast_iff' p 3 4).mpr hp4
  have hmod := congrArg (Int.cast : ℤ → ZMod 4) h
  push_cast at hmod
  rw [pow_mul, show (2 : ZMod 4) ^ 2 = 0 by decide, zero_pow (by omega : k ≠ 0),
    zero_mul, zero_pow hx, hp, hy.neg_one_pow, zero_sub] at hmod
  exact (by decide : ∀ a : ZMod 4, -1 ≠ a ^ 2) z hmod

private theorem impossible_mod_prime {p k x y z : ℕ} (hq : (2 * p - 1).Prime) (hp4 : p % 4 = 3)
    (hx : x ≠ 0) (hy : Odd y)
    (h : ((2 : ℤ) ^ (2 * k) * (2 * p - 1)) ^ x - (p : ℤ) ^ y = (z : ℤ) ^ 2) : False := by
  let q := 2 * p - 1
  have : Fact q.Prime := ⟨hq⟩
  have hq8 : q % 8 = 5 := by
    dsimp [q]
    omega
  have hpair : 2 * (p : ZMod q) - 1 = 0 := by
    simpa only [q, Nat.cast_sub (by omega : 1 ≤ 2 * p), Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one] using ZMod.natCast_self q
  obtain ⟨m, rfl⟩ := hy
  have hmod := congrArg (Int.cast : ℤ → ZMod q) h
  push_cast at hmod
  rw [hpair, mul_zero, zero_pow hx, zero_sub] at hmod
  have hscaled : (2 : ZMod q) ^ (2 * m + 1) * (z : ZMod q) ^ 2 = -1 := by
    rw [← hmod, mul_neg, ← mul_pow, sub_eq_zero.mp hpair, one_pow]
  have hsquare : IsSquare (-2 : ZMod q) := by
    refine ⟨2 ^ (m + 1) * z, ?_⟩
    rw [pow_succ, pow_mul'] at hscaled
    rw [pow_succ]
    linear_combination -2 * hscaled
  have := (ZMod.exists_sq_eq_neg_two_iff (by omega : q ≠ 2)).mp hsquare
  omega

end prime_pair_two_pow_even_mul_pow_sub_pow_eq_sq_iff

open prime_pair_two_pow_even_mul_pow_sub_pow_eq_sq_iff

/-- **Squares of the form $(2^{2k}(2p - 1))^x - p^y$ for prime pairs.** Let $p$ be a prime with
$p \equiv 3 \pmod 4$ such that $2p - 1$ is prime, and let $k \ge 1$ be an integer. Then
non-negative integers $x$, $y$ and $z$ satisfy $(2^{2k}(2p - 1))^x - p^y = z^2$ if and only if
$(x, y, z) = (0, 0, 0)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 6. -/
public theorem prime_pair_two_pow_even_mul_pow_sub_pow_eq_sq_iff {p k : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp4 : p % 4 = 3) (hk : 1 ≤ k) (x y z : ℕ) :
    ((2 : ℤ) ^ (2 * k) * (2 * p - 1)) ^ x - (p : ℤ) ^ y = (z : ℤ) ^ 2 ↔
      (x, y, z) = (0, 0, 0) := by
  constructor
  · intro h
    obtain rfl : x = 0 := by
      by_contra hx
      exact impossible_mod_prime hq hp4 hx (odd_exponent_mod_four hp4 hk hx h) h
    rw [pow_zero] at h
    obtain rfl : y = 0 := by
      by_contra hy
      have hp' : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
      have := one_lt_pow₀ hp' hy
      linarith [sq_nonneg (z : ℤ)]
    simp only [pow_zero, sub_self] at h
    obtain rfl : z = 0 := by exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h.symm
    rfl
  · rintro ⟨⟩
    simp

end MetaMathlibExt
