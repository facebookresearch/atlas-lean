/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import MathlibExt.NumberTheory.PrimePairOneAddTwoPowMulPowEqSq

/-!
# No squares of the form `p ^ x + (2 ^ (2 * k + 1) * (2 * p - 1)) ^ y`

For primes `p` and `2 * p - 1` with `p ≡ 5, 7 (mod 8)`, the sum
`p ^ x + (2 ^ (2 * k + 1) * (2 * p - 1)) ^ y` is never a square. Reduction modulo three
forces `p ≡ 1` and the exponent `y` to be odd. With `x = 0` the equation contradicts the
classification of `1 + (2 ^ k * (2 * p - 1)) ^ y = z ^ 2`, and with `x ≥ 1` the odd `y`
exhibits `-2` as a square modulo `p`, impossible for `p ≡ 5, 7 (mod 8)`.

Proves Theorem 2 of Jing Zhang and Yuan Li, *On the Equation
(-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024),
Article A64.
-/

namespace MetaMathlibExt

namespace prime_pair_pow_add_two_pow_odd_mul_pow_ne_sq

/-- For the prime pair `p`, `2 * p - 1` with `p ≡ 5, 7 (mod 8)`, we have `p ≡ 1 (mod 3)`:
`p` exceeds three, and `p ≡ 2 (mod 3)` would make `2 * p - 1` a proper multiple of three. -/
private theorem prime_mod_three_eq_one {p : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp8 : p % 8 = 5 ∨ p % 8 = 7) : p % 3 = 1 := by
  have hp5 : 5 ≤ p := by omega
  have hq9 : 9 ≤ 2 * p - 1 := by omega
  have hp3ne : p % 3 ≠ 0 := by
    intro h0
    have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have := (Nat.dvd_prime hp).mp hdvd
    omega
  have hp3ne2 : p % 3 ≠ 2 := by
    intro h2
    have hq0 : (2 * p - 1) % 3 = 0 := by omega
    have hdvd : 3 ∣ 2 * p - 1 := Nat.dvd_of_mod_eq_zero hq0
    have := (Nat.dvd_prime hq).mp hdvd
    omega
  omega

/-- Modulo three, `p ^ x + (2 ^ (2 * k + 1) * (2 * p - 1)) ^ y` is `1 + (-1) ^ y`, so an even
`y` would give the non-square `2`; hence `y` is odd. -/
private theorem odd_of_eq {p k x y z : ℕ} (hp : p.Prime) (hq : (2 * p - 1).Prime)
    (hp8 : p % 8 = 5 ∨ p % 8 = 7)
    (h : p ^ x + (2 ^ (2 * k + 1) * (2 * p - 1)) ^ y = z ^ 2) : Odd y := by
  refine (Nat.even_or_odd y).resolve_left fun hy => ?_
  have hp3 : p % 3 = 1 := prime_mod_three_eq_one hp hq hp8
  have hq3 : (2 * p - 1) % 3 = 1 := by omega
  have hpm : (p : ZMod 3) = 1 := (ZMod.natCast_eq_natCast_iff' p 1 3).mpr (by omega)
  have hqm : ((2 * p - 1 : ℕ) : ZMod 3) = 1 :=
    (ZMod.natCast_eq_natCast_iff' _ 1 3).mpr (by omega)
  have h2k : (2 : ZMod 3) ^ (2 * k + 1) = 2 := by
    rw [pow_add, pow_mul, show (2 : ZMod 3) ^ 2 = 1 by decide, one_pow, one_mul,
      pow_one]
  obtain ⟨t, rfl⟩ := hy
  have hmod := congrArg (Nat.cast : ℕ → ZMod 3) h
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, hpm, hqm, h2k,
    one_pow, mul_one] at hmod
  rw [show t + t = 2 * t by omega, pow_mul,
    show (2 : ZMod 3) ^ 2 = 1 by decide, one_pow] at hmod
  exact (by decide : ∀ a : ZMod 3, 1 + 1 ≠ a ^ 2) z hmod

/-- With `x ≥ 1` and `y` odd, the equation makes `-2` a square modulo `p`: the base is
`-2` times a square, and the odd power preserves this shape. Since `p ≡ 5, 7 (mod 8)`,
`-2` is a non-square, giving a contradiction. -/
private theorem false_of_odd_of_pos {p k x y z : ℕ} (hp : p.Prime)
    (hp8 : p % 8 = 5 ∨ p % 8 = 7) (hx : x ≠ 0)
    (h : p ^ x + (2 ^ (2 * k + 1) * (2 * p - 1)) ^ y = z ^ 2) (hy : Odd y) :
    False := by
  have hp2 : p ≠ 2 := by omega
  have h2p1 : 1 ≤ 2 * p := by omega
  have := Fact.mk hp
  obtain ⟨t, rfl⟩ := hy
  have hq : ((2 * p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub h2p1, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self]
    simp
  have hbase : ((2 ^ (2 * k + 1) * (2 * p - 1) : ℕ) : ZMod p)
      = -2 * (2 ^ k : ZMod p) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hq]
    rw [show (2 : ZMod p) ^ (2 * k + 1) = 2 * (2 ^ k : ZMod p) ^ 2 by ring]
    ring
  have h2ne : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
  have hmod := congrArg (Nat.cast : ℕ → ZMod p) h
  simp only [Nat.cast_add, Nat.cast_pow] at hmod
  rw [ZMod.natCast_self, zero_pow hx, zero_add, hbase] at hmod
  have hexp : (-2 * (2 ^ k : ZMod p) ^ 2) ^ (2 * t + 1)
      = -2 * ((-2) ^ t * (2 ^ k : ZMod p) ^ (2 * t + 1)) ^ 2 := by
    ring
  rw [hexp] at hmod
  have hk0 : (2 : ZMod p) ^ k ≠ 0 := pow_ne_zero k h2ne
  have hW : ((-2) ^ t * (2 ^ k : ZMod p) ^ (2 * t + 1)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero t (neg_ne_zero.mpr h2ne)) (pow_ne_zero _ hk0)
  have hW2 : ((-2) ^ t * (2 ^ k : ZMod p) ^ (2 * t + 1)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hW
  have hsq : IsSquare (-2 : ZMod p) := by
    refine ⟨(z : ZMod p) * ((-2) ^ t * (2 ^ k : ZMod p) ^ (2 * t + 1))⁻¹, ?_⟩
    calc -2 = (-2 * ((-2) ^ t * (2 ^ k : ZMod p) ^ (2 * t + 1)) ^ 2) *
          (((-2) ^ t * (2 ^ k : ZMod p) ^ (2 * t + 1)) ^ 2)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hW2, mul_one]
        _ = (z : ZMod p) ^ 2 * (((-2) ^ t * (2 ^ k : ZMod p) ^ (2 * t + 1)) ^ 2)⁻¹ := by
            rw [hmod]
        _ = (z : ZMod p) * ((-2) ^ t * (2 ^ k : ZMod p) ^ (2 * t + 1))⁻¹ *
            ((z : ZMod p) * ((-2) ^ t * (2 ^ k : ZMod p) ^ (2 * t + 1))⁻¹) := by
            rw [← inv_pow]
            ring
  have := (ZMod.exists_sq_eq_neg_two_iff hp2).mp hsq
  omega

end prime_pair_pow_add_two_pow_odd_mul_pow_ne_sq

open prime_pair_pow_add_two_pow_odd_mul_pow_ne_sq

/-- **No squares of the form $p^x + (2^{2k+1}(2p - 1))^y$ for prime pairs with
$p \equiv 5, 7 \pmod 8$.** Let $p$ be a prime with $p \equiv 5 \pmod 8$ or $p \equiv 7 \pmod 8$
such that $2p - 1$ is prime. Then for all non-negative integers $k$, $x$, $y$ and $z$,
$p^x + (2^{2k+1}(2p - 1))^y \ne z^2$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 2. -/
public theorem prime_pair_pow_add_two_pow_odd_mul_pow_ne_sq {p : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp8 : p % 8 = 5 ∨ p % 8 = 7) (k x y z : ℕ) :
    p ^ x + (2 ^ (2 * k + 1) * (2 * p - 1)) ^ y ≠ z ^ 2 := by
  intro h
  have hy : Odd y := odd_of_eq hp hq hp8 h
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp only [pow_zero] at h
    have hk : 1 ≤ 2 * k + 1 := by omega
    have hp2 : p ≠ 2 := by omega
    have hcon := (one_add_two_pow_mul_pow_eq_sq_iff hp hp2 hq hk y z).mp h
    simp only [Prod.mk.injEq] at hcon
    omega
  · exact false_of_odd_of_pos hp hp8 hx.ne' h hy

end MetaMathlibExt
