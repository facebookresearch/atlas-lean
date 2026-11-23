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
# Squares of the form `p ^ x - (2 ^ (2 * k + 1) * (2 * p - 1)) ^ y` for prime pairs

Let `p ≡ 3 (mod 8)` be a prime. Modulo `p` we have `2 * p - 1 ≡ -1`, so
`2 ^ (2 * k + 1) * (2 * p - 1) ≡ -2 * 4 ^ k`, a nonzero square because `-2` is a square modulo
`p`. If `x ≥ 1`, the equation `p ^ x - (2 ^ (2 * k + 1) * (2 * p - 1)) ^ y = z ^ 2` therefore
makes `-1` a square modulo `p`, which is impossible as `p ≡ 3 (mod 4)`. With `x = 0` the left side
is negative unless `y = 0`, and then `z = 0`.

The argument does not use the hypothesis that `2 * p - 1` is prime.
-/

namespace MetaMathlibExt

namespace prime_pair_pow_sub_two_pow_odd_mul_pow_eq_sq_iff

/-- For a prime `p ≡ 3 (mod 8)`, the equation `p ^ x - (2 ^ (2 * k + 1) * (2 * p - 1)) ^ y = z ^ 2`
forces `x = 0`: modulo `p` it would otherwise exhibit `-1` as a square. -/
private theorem exponent_eq_zero {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3) {k x y z : ℕ}
    (h : (p : ℤ) ^ x - ((2 : ℤ) ^ (2 * k + 1) * (2 * p - 1)) ^ y = (z : ℤ) ^ 2) : x = 0 := by
  have := Fact.mk hp
  by_contra hx
  obtain ⟨c, hc⟩ := (ZMod.exists_sq_eq_neg_two_iff (p := p) (by omega)).2 (Or.inr hp8)
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact h2 (neg_eq_zero.mp (by simpa using hc))
  have hsq : (2 : ZMod p) ^ (2 * k + 1) * (2 * 0 - 1) = (c * 2 ^ k) ^ 2 := by
    rw [mul_pow, sq c, ← hc, ← pow_mul, pow_succ]
    ring
  have hmod := congrArg (Int.cast : ℤ → ZMod p) h
  push_cast at hmod
  rw [ZMod.natCast_self, zero_pow hx, hsq, ← pow_mul, mul_comm 2 y, pow_mul, zero_sub] at hmod
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (pow_ne_zero y (mul_ne_zero hc0 (pow_ne_zero k h2)))
    hmod.symm (by omega)

end prime_pair_pow_sub_two_pow_odd_mul_pow_eq_sq_iff

open prime_pair_pow_sub_two_pow_odd_mul_pow_eq_sq_iff

set_option linter.unusedVariables false in
/-- **Squares of the form $p^x - (2^{2k+1}(2p - 1))^y$ for prime pairs.** Let $p$ be a prime with
$p \equiv 3 \pmod 8$ such that $2p - 1$ is prime, and let $k$ be a non-negative integer. Then
non-negative integers $x$, $y$ and $z$ satisfy $p^x - (2^{2k+1}(2p - 1))^y = z^2$ if and only if
$(x, y, z) = (0, 0, 0)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 9. -/
public theorem prime_pair_pow_sub_two_pow_odd_mul_pow_eq_sq_iff {p : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp8 : p % 8 = 3) (k x y z : ℕ) :
    (p : ℤ) ^ x - ((2 : ℤ) ^ (2 * k + 1) * (2 * p - 1)) ^ y = (z : ℤ) ^ 2 ↔
      (x, y, z) = (0, 0, 0) := by
  constructor
  · intro h
    obtain rfl := exponent_eq_zero hp hp8 h
    obtain rfl : y = 0 := by
      by_contra hy
      have hpow : (2 : ℤ) ≤ 2 ^ (2 * k + 1) := le_self_pow₀ (by norm_num) (by omega)
      have hp3 : (3 : ℤ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
      have hA : 1 < (2 : ℤ) ^ (2 * k + 1) * (2 * p - 1) := by nlinarith
      have := one_lt_pow₀ hA hy
      nlinarith [sq_nonneg (z : ℤ)]
    simp only [pow_zero, sub_self] at h
    obtain rfl : z = 0 := by exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h.symm
    rfl
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp

end MetaMathlibExt
