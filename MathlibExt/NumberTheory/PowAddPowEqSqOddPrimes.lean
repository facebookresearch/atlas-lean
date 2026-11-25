/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.LegendreSymbol.Basic
import MathlibExt.NumberTheory.PrimePowAddOneEqSq

/-!
# Squares of the form `p^x + (p + a)^y` when `a ≡ 0 (mod 4)` and `p ∣ a + 1`

`pow_add_pow_eq_sq` shows that if `p ≠ 2, 3` and `p + a` are primes with `a ≡ 0 (mod 4)` and
`p ∣ a + 1`, then every solution of `p^x + (p + a)^y = z^2` in natural numbers has `x = 0`,
`y = 1` and `z^2 = p + a + 1`. The ATLAS wiki attributes this result to Theorem 6 of Shalini
Choudhury and Naba Kanta Sarma, "On the Diophantine Equations `(p+a)^x + p^y = z^2` and
`(p+a)^x - p^y = z^2` where `p` and `p+a` Are Odd Primes", *INTEGERS* 26 (2026), Article A87
(<https://math.colgate.edu/~integers/vol26.html>).

When `x = 0` the equation says that a power of the prime `p + a` is one less than a square, which
`MetaMathlibExt.prime_pow_add_one_eq_sq_iff` classifies. When `x > 0` there is no solution.
Since `p ≡ p + a (mod 4)`, the case `p ≡ 1 (mod 4)` would make the left side `2` modulo four.
Since `p + a ≡ -1 (mod p)`, the equation gives `z^2 ≡ (-1)^y (mod p)`, and `-1` is not a square
modulo a prime `p ≡ 3 (mod 4)`, so `y = 2k` is even. Writing `z = (p + a)^k + d` turns the
equation into `p^x = d (2 (p + a)^k + d)`, so both factors are powers of `p`. As
`(p + a)^k ≡ ±1 (mod p)`, either `d = 1` and `p` divides `2 (p + a)^k + 1 ≡ 3` or `-1`, or `p`
divides both factors and hence their difference `2 (p + a)^k ≡ ±2`; each case contradicts
`p ≠ 2, 3`.

The case the conclusion leaves open does not occur either: `p + a + 1` is a square only when
`p + a = 3`, whereas `a ≥ 4` because `a ≡ 0 (mod 4)` and `p ∣ a + 1`. So the equation has no
solution at all under these hypotheses.
-/

public section

namespace MathlibExt.NumberTheory.ExponentialDiophantineWanted

/-- **Solutions of $p^x + (p + a)^y = z^2$ for odd primes $p$ and $p + a$.** Let $p$ be a
prime with $p \ne 2$ and $p \ne 3$, and let $a$ be a natural number such that $p + a$ is
prime, $a \equiv 0 \pmod 4$ and $p$ divides $a + 1$. If natural numbers $x$, $y$ and $z$
satisfy $p^x + (p + a)^y = z^2$, then $x = 0$, $y = 1$ and $z^2 = p + a + 1$.

Source: Shalini Choudhury and Naba Kanta Sarma, "On the
Diophantine Equations `(p+a)^x + p^y = z^2` and
`(p+a)^x - p^y = z^2` where `p` and `p+a` Are Odd
Primes", Theorem 6. -/
theorem pow_add_pow_eq_sq (p a x y z : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpa : (p + a).Prime) (ha4 : a % 4 = 0)
    (hap : p ∣ a + 1) (h : p ^ x + (p + a) ^ y = z ^ 2) :
    x = 0 ∧ y = 1 ∧ z ^ 2 = p + a + 1 := by
  -- `x = 0`: `(p + a) ^ y + 1 = z ^ 2` forces `p + a = 3`, `y = 1` and `z = 2`.
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [pow_zero, add_comm] at h
    rcases (MetaMathlibExt.prime_pow_add_one_eq_sq_iff hpa y z).1 h with h' | h' <;>
      simp only [Prod.mk.injEq] at h'
    · have := hp.two_le
      omega
    · obtain ⟨hq, rfl, rfl⟩ := h'
      exact ⟨rfl, rfl, by rw [hq]; rfl⟩
  -- `x > 0`: there is no solution.
  exfalso
  have := Fact.mk hp
  -- Modulo four, `p ≡ p + a`, and `p ≡ 1` would make the left side `2`: so `p ≡ 3 (mod 4)`.
  have hp4 : p % 4 = 3 := by
    have hodd := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    refine (by omega : p % 4 = 1 ∨ p % 4 = 3).resolve_left fun h1 => ?_
    have hx4 : p ^ x % 4 = 1 := by simp [Nat.pow_mod, h1]
    have hy4 : (p + a) ^ y % 4 = 1 := by simp [Nat.pow_mod, show (p + a) % 4 = 1 by omega]
    have hz : z ^ 2 % 4 = 0 ∨ z ^ 2 % 4 = 1 := by
      rcases (by omega : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3) with hr | hr | hr | hr <;>
        simp [Nat.pow_mod, hr]
    omega
  -- Modulo `p`, `p + a ≡ -1` and `p ^ x ≡ 0`.
  have hq : ((p + a : ℕ) : ZMod p) = -1 := by
    refine eq_neg_of_add_eq_zero_left ?_
    rw [← Nat.cast_add_one, ZMod.natCast_eq_zero_iff, add_assoc]
    exact dvd_add dvd_rfl hap
  have hpx : ((p ^ x : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_pow, ZMod.natCast_self, zero_pow hx.ne']
  -- So `z ^ 2 ≡ (-1) ^ y (mod p)`; as `-1` is not a square modulo `p ≡ 3 (mod 4)`, `y` is even.
  obtain ⟨k, rfl⟩ : Even y := by
    refine (Nat.even_or_odd y).resolve_right fun hodd => ?_
    have hzp := congrArg (Nat.cast : ℕ → ZMod p) h
    rw [Nat.cast_add, hpx, zero_add, Nat.cast_pow, hq, hodd.neg_one_pow] at hzp
    exact ZMod.exists_sq_eq_neg_one_iff.mp ⟨z, by rw [hzp, Nat.cast_pow, sq]⟩ hp4
  -- With `w = (p + a) ^ k ≡ (-1) ^ k` and `z = w + d`, the equation is `p ^ x = d * (2 * w + d)`.
  obtain ⟨w, hw⟩ : ∃ w, w = (p + a) ^ k := ⟨_, rfl⟩
  have hwp : (w : ZMod p) = (-1) ^ k := by rw [hw, Nat.cast_pow, hq]
  rw [pow_add, ← hw, ← sq] at h
  have hwz : w < z := by
    have := pow_pos hp.pos x
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) (by omega)
  obtain ⟨d, rfl⟩ : ∃ d, z = w + d := ⟨z - w, by omega⟩
  have hfac : p ^ x = d * (2 * w + d) := by nlinarith only [h]
  -- Both factors are powers of `p`: `d = p ^ i` and `2 * w + d = p ^ j`.
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hfac.symm)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro_left _ hfac.symm)
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · -- `d = 1`: then `p` divides `2 * w + 1 ≡ 3` or `-1`.
    rw [pow_zero, one_mul] at hfac
    have h0 := congrArg (Nat.cast : ℕ → ZMod p) hfac
    rw [hpx, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, hwp] at h0
    rcases neg_one_pow_eq_or (ZMod p) k with hk | hk <;> rw [hk] at h0
    · have h3 : ((3 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; linear_combination -h0
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
        ((ZMod.natCast_eq_zero_iff 3 p).1 h3))
    · exact one_ne_zero (by linear_combination h0 : (1 : ZMod p) = 0)
  · -- `p ∣ d`: then `j > 0`, so `p` divides `2 * w + d` and hence `2 * w ≡ ±2`.
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hj
      have := one_lt_pow₀ hp.one_lt hi.ne'
      omega
    have h0 := congrArg (Nat.cast : ℕ → ZMod p) hj
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_pow, ZMod.natCast_self,
      zero_pow hi.ne', zero_pow hj0, add_zero, hwp] at h0
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_ofNat]
      rcases neg_one_pow_eq_or (ZMod p) k with hk | hk <;> rw [hk] at h0
      · linear_combination h0
      · linear_combination -h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      ((ZMod.natCast_eq_zero_iff 2 p).1 h2))

end MathlibExt.NumberTheory.ExponentialDiophantineWanted
