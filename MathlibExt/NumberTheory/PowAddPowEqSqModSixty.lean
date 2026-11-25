/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import MathlibExt.NumberTheory.PowAddPowEqSqEvenExponent
import MathlibExt.NumberTheory.PowAddPowEqSqOppositeParity
import MathlibExt.NumberTheory.ThreePowAddThirtyfivePow

/-!
# Solutions of `n^x + (5p)^y = z^2` in two residue classes modulo 60

`solutions_mod_sixty` classifies the solutions when `n` is 3 or 27 modulo 60 and `p` is a prime
congruent to 7 modulo 12. For positive exponents, reduction modulo 5 forces `x` to be even,
modulo 4 then forces `y` to be odd, and modulo 3 this makes the square equal to −1.
-/

namespace MathlibExt.NumberTheory.PowAddPowEqSqWanted

/-- If a positive power of an odd number is one less than a square, its exponent is one.
The two odd factors of `z² - 1` are coprime powers differing by two. -/
private lemma exp_eq_one_of_odd_base {n x z : ℕ} (hn : Odd n) (hx : x ≠ 0)
    (h : n ^ x + 1 = z ^ 2) : x = 1 := by
  obtain _ | k := z
  · simp at h
  have hfac : k * (k + 2) = n ^ x := by nlinarith only [h]
  obtain ⟨hk, hk'⟩ := Nat.odd_mul.mp (hfac ▸ hn.pow)
  have hcop : k.Coprime (k + 2) := Nat.coprime_self_add_right.mpr hk.coprime_two_right
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.gcd_eq_one) hfac
  obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.symm.gcd_eq_one)
    (by rwa [mul_comm (k + 2) k])
  have hab : a < b := (Nat.pow_lt_pow_iff_left hx).mp (by omega)
  have haOdd := (Nat.odd_pow_iff hx).mp (ha ▸ hk)
  have hbOdd := (Nat.odd_pow_iff hx).mp (hb ▸ hk')
  have hgap : a + 2 ≤ b := by
    rw [Nat.odd_iff] at haOdd hbOdd
    omega
  have hle : a ^ x + 2 ^ x ≤ b ^ x :=
    (pow_add_pow_le (Nat.zero_le a) (Nat.zero_le 2) hx).trans (Nat.pow_le_pow_left hgap x)
  have hxle : x ≤ 1 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (show 2 ^ x ≤ 2 ^ 1 by omega)
  omega

-- The residue classes already rule out positive exponents without the coprimality assumptions.
set_option linter.unusedVariables false in
/-- **Solutions of $n^x + (5p)^y = z^2$ for $n \equiv 3, 27 \pmod{60}$ and $p \equiv 7 \pmod{12}$.**
Let $p$ be a prime with $p \equiv 7 \pmod{12}$, and let $n$ be a natural number with
$n \equiv 3 \pmod{60}$ or $n \equiv 27 \pmod{60}$ such that $\gcd(n, p) = 1$ and
$\gcd(n, 5p - 1) = 1$. For natural numbers $x$, $y$, $z$, $n^x + (5p)^y = z^2$ holds if and
only if either $x = 0$, $y = 1$ and $z^2 = 5p + 1$, or $x = 1$, $y = 0$ and $z^2 = n + 1$.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Theorem 4. -/
public theorem solutions_mod_sixty (n p x y z : ℕ) (hp : p.Prime)
    (hn : n % 60 = 3 ∨ n % 60 = 27) (hp12 : p % 12 = 7)
    (h1 : Nat.Coprime n p) (h2 : Nat.Coprime n (5 * p - 1)) :
    n ^ x + (5 * p) ^ y = z ^ 2 ↔
      (x = 0 ∧ y = 1 ∧ z ^ 2 = 5 * p + 1) ∨
        (x = 1 ∧ y = 0 ∧ z ^ 2 = n + 1) := by
  constructor
  · intro h
    by_cases hx : x = 0
    · subst x
      exact Or.inl ⟨rfl, (one_add_pow_eq_sq p y z hp (by omega)).mp (by simpa using h)⟩
    by_cases hy : y = 0
    · subst y
      simp only [pow_zero] at h
      have hx' := exp_eq_one_of_odd_base (Nat.odd_iff.mpr (by omega)) hx h
      exact Or.inr ⟨hx', rfl, by simpa [hx'] using h.symm⟩
    have heven := Nat.even_iff.mp (even_of_pos_exp n p x y z hp (by omega) (by omega) h)
    have hpar := opposite_parity n p x y z hp (by omega) (by omega) h
    have hodd : Odd y := Nat.odd_iff.mpr (by omega)
    have hn3 : (n : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff n 3).mpr (by omega)
    have hp3 : ((5 * p : ℕ) : ZMod 3) = -1 := by
      rw [← ZMod.natCast_mod, show 5 * p % 3 = 2 by omega]
      decide
    have hz : (z : ZMod 3) ^ 2 = -1 := calc
      _ = (n : ZMod 3) ^ x + ((5 * p : ℕ) : ZMod 3) ^ y := by
        simpa only [Nat.cast_add, Nat.cast_pow] using congrArg (Nat.cast : ℕ → ZMod 3) h.symm
      _ = -1 := by rw [hn3, hp3, zero_pow hx, zero_add, hodd.neg_one_pow]
    exact absurd hz ((by decide : ∀ r : ZMod 3, r ^ 2 ≠ -1) z)
  · rintro (⟨rfl, rfl, hz⟩ | ⟨rfl, rfl, hz⟩) <;> simp [hz, add_comm]

end MathlibExt.NumberTheory.PowAddPowEqSqWanted
