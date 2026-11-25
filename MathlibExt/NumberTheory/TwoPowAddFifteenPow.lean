/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import MathlibExt.NumberTheory.PowAddPowEqSq
import MathlibExt.NumberTheory.ThreePowAddThirtyfivePow

/-!
# Solutions of `2^x + 15^y = z^2`

The theorem `two_pow_add_fifteen_pow` classifies all natural-number solutions.
For positive exponents, squares modulo three and four force both exponents to be even.
Factoring the difference of squares then reduces the equation to `1 + 15^k = w^2`.
-/

namespace MathlibExt.NumberTheory.PowAddPowEqSqWanted

/-- If the square of an odd number plus a power of two is a square, its root is two larger. -/
private lemma root_eq_add_two {a x z : ℕ} (ha : Odd a) (h : 2 ^ x + a ^ 2 = z ^ 2) :
    z = a + 2 := by
  have hlt : a < z := (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp (by
    have := Nat.two_pow_pos x
    omega)
  have hfac : (z + a) * (z - a) = 2 ^ x := by
    rw [← Nat.sq_sub_sq, ← h, Nat.add_sub_cancel]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ hfac)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro_left _ hfac)
  have ha' := Nat.odd_iff.mp ha
  -- The larger factor exceeds two, so it is a multiple of four.
  have hfour : 4 ∣ z + a := by
    have hi₂ : 1 < i := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp (by
      rw [pow_one, ← hi]
      omega)
    rw [hi]
    exact pow_dvd_pow 2 hi₂
  -- The factors differ by twice an odd number, so the smaller is two modulo four.
  rcases j with _ | _ | j <;> simp only [pow_zero, pow_succ] at hj <;> omega

private lemma positive_solution {x y z : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : 2 ^ x + 15 ^ y = z ^ 2) : x = 6 ∧ y = 2 ∧ z = 17 := by
  have hex : Even x := (Nat.even_or_odd x).resolve_right fun ho => by
    have hm := congrArg (Nat.cast : ℕ → ZMod 3) h
    push_cast at hm
    rw [show (2 : ZMod 3) = -1 by decide, ho.neg_one_pow, show (15 : ZMod 3) = 0 by decide,
      zero_pow hy, add_zero] at hm
    exact (by decide : ∀ r : ZMod 3, -1 ≠ r ^ 2) z hm
  obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hex
  obtain _ | k := k
  · exact (hx rfl).elim
  have hey : Even y := (Nat.even_or_odd y).resolve_right fun ho => by
    have hm := congrArg (Nat.cast : ℕ → ZMod 4) h
    push_cast at hm
    rw [pow_mul, show (2 : ZMod 4) ^ 2 = 0 by decide, zero_pow (Nat.succ_ne_zero k),
      show (15 : ZMod 4) = -1 by decide, ho.neg_one_pow, zero_add] at hm
    exact (by decide : ∀ r : ZMod 4, -1 ≠ r ^ 2) z hm
  obtain ⟨l, rfl⟩ := even_iff_exists_two_mul.mp hey
  rw [pow_mul' 15] at h
  have hz := root_eq_add_two ((by decide : Odd 15).pow) h
  rw [pow_mul' 2, pow_succ (2 : ℕ) k, hz] at h
  have hs : 1 + 15 ^ l = (2 ^ k) ^ 2 := by nlinarith only [h]
  obtain ⟨rfl, hsquare⟩ := (one_add_pow_eq_sq 3 l (2 ^ k) (by decide) (by decide)).mp hs
  have hk : k = 2 := Nat.pow_right_injective (by decide : 2 ≤ 2)
    (Nat.pow_left_injective (by decide : 2 ≠ 0) hsquare)
  subst k
  exact ⟨rfl, rfl, hz⟩

/-- **Solutions of $2^x + 15^y = z^2$.** The natural numbers $x$, $y$, $z$ with
$2^x + 15^y = z^2$ are exactly $(x, y, z) = (3, 0, 3)$, $(0, 1, 4)$ and $(6, 2, 17)$.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Corollary 3. -/
public theorem two_pow_add_fifteen_pow (x y z : ℕ) :
    2 ^ x + 15 ^ y = z ^ 2 ↔
      (x = 3 ∧ y = 0 ∧ z = 3) ∨ (x = 0 ∧ y = 1 ∧ z = 4) ∨
        (x = 6 ∧ y = 2 ∧ z = 17) := by
  constructor
  · intro h
    by_cases hy : y = 0
    · subst y
      obtain ⟨rfl, rfl⟩ := (MetaMathlibExt.two_pow_add_one_eq_sq x z).mp h
      exact Or.inl ⟨rfl, rfl, rfl⟩
    by_cases hx : x = 0
    · subst x
      obtain ⟨rfl, hz⟩ := (one_add_pow_eq_sq 3 y z (by decide) (by decide)).mp h
      exact Or.inr (Or.inl ⟨rfl, rfl, Nat.pow_left_injective (by decide : 2 ≠ 0) hz⟩)
    exact Or.inr (Or.inr (positive_solution hx hy h))
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> rfl

end MathlibExt.NumberTheory.PowAddPowEqSqWanted
