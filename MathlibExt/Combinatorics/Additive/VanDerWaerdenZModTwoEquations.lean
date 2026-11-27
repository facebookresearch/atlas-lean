/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Two equations modulo primes congruent to three modulo four

For a prime `n > 3` with `n % 4 = 3`, there are nonzero `x, y : ZMod n` and an exponent
`r ∈ {2, 3}` such that `x + r * y = 0` and `x * y ^ r = 1`.

## References

* Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem to Some
  Symmetric Functions*, INTEGERS 26 (2026), Article A25, pp. 1–12, Lemma 6.
-/

namespace MetaMathlibExt

/-- **Nonzero solutions of a two-equation system modulo primes greater than 3 congruent to 3
mod 4.** Let $n > 3$ be a prime with $n \equiv 3 \pmod 4$. Then there are nonzero
$x, y \in \mathbb{Z}/n\mathbb{Z}$ and an integer $r \in \{2, 3\}$ such that $x + ry = 0$ and
$xy^r = 1$ in $\mathbb{Z}/n\mathbb{Z}$.

The source prints the second equation as $xy r = 1$; it is read as $xy^r = 1$, as in the proof,
whose first case computes $xy^2 = x^3/4 = 1$.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 6
(`integers-2026-A25-lem-6`). -/
public theorem exists_add_mul_eq_zero_mul_pow_eq_one {n : ℕ} (hp : n.Prime)
    (h3 : 3 < n) (h4 : n % 4 = 3) :
    ∃ x y : ZMod n, x ≠ 0 ∧ y ≠ 0 ∧ ∃ r : ℕ, (r = 2 ∨ r = 3) ∧
      x + r * y = 0 ∧ x * y ^ r = 1 := by
  let : Fact n.Prime := ⟨hp⟩
  have htwo : (2 : ZMod n) ≠ 0 :=
    mt (ZMod.natCast_eq_zero_iff 2 n).mp (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have hthree : (3 : ZMod n) ≠ 0 :=
    mt (ZMod.natCast_eq_zero_iff 3 n).mp (Nat.not_dvd_of_pos_of_lt (by decide) h3)
  have hcard : Fintype.card (ZMod n)ˣ = n - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]
  by_cases hd : 3 ∣ n - 1
  · -- A nontrivial cube root of unity gives a square root of `-3`.
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := (ZMod n)ˣ) 3 (by rwa [hcard])
    let t : ZMod n := u
    have ht : orderOf t = 3 := orderOf_units.trans hu
    have ht1 : t ≠ 1 := by
      intro h
      simp [h] at ht
    have ht3 : t ^ 3 = 1 := by rw [← ht, pow_orderOf_eq_one]
    have hquad : t ^ 2 + t + 1 = 0 := by
      have hfactor : (t - 1) * (t ^ 2 + t + 1) = 0 := by
        linear_combination ht3
      exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr ht1)
    let z : ZMod n := 2 * t + 1
    have hz : z ^ 2 = -3 := by
      dsimp [z]
      linear_combination 4 * hquad
    have hz0 : z ≠ 0 := by
      intro h
      apply hthree
      simpa [h] using hz.symm
    let a : ZMod n := 3 * z
    let x : ZMod n := a ^ ((n + 1) / 4)
    have ha : a ≠ 0 := mul_ne_zero hthree hz0
    have hx : x ≠ 0 := pow_ne_zero _ ha
    have hx4 : x ^ 4 = -(3 : ZMod n) ^ 3 := calc
      x ^ 4 = a ^ (n + 1) := by
        dsimp [x]
        rw [← pow_mul, show (n + 1) / 4 * 4 = n + 1 by omega]
      _ = a ^ 2 := by
        rw [show n + 1 = n - 1 + 2 by omega, pow_add, ZMod.pow_card_sub_one_eq_one ha, one_mul]
      _ = -(3 : ZMod n) ^ 3 := by
        dsimp [a]
        rw [mul_pow, hz]
        ring
    refine ⟨x, -x / 3, hx, div_ne_zero (neg_ne_zero.mpr hx) hthree, 3, Or.inr rfl, ?_, ?_⟩
    · rw [Nat.cast_ofNat]
      field_simp
      ring
    · calc
        x * (-x / 3) ^ 3 = -(x ^ 4) / 3 ^ 3 := by
          rw [div_pow, ← mul_div_assoc]
          congr 1
          ring
        _ = 1 := by rw [hx4, neg_neg, div_self (pow_ne_zero _ hthree)]
  · -- Otherwise cubing is a bijection on the units, so `4` has a cube root.
    have hcop : (Nat.card (ZMod n)ˣ).Coprime 3 := by
      rw [Nat.card_eq_fintype_card, hcard, Nat.coprime_comm]
      exact Nat.prime_three.coprime_iff_not_dvd.mpr hd
    have hfour : (4 : ZMod n) ≠ 0 := by
      rw [show (4 : ZMod n) = 2 ^ 2 by ring]
      exact pow_ne_zero _ htwo
    obtain ⟨u, hu⟩ := hcop.pow_left_bijective.surjective (Units.mk0 4 hfour)
    let x : ZMod n := u
    have hx : x ≠ 0 := Units.ne_zero u
    have hx3 : x ^ 3 = 4 := by
      simpa [x] using congrArg (fun v : (ZMod n)ˣ => (v : ZMod n)) hu
    refine ⟨x, -x / 2, hx, div_ne_zero (neg_ne_zero.mpr hx) htwo, 2, Or.inl rfl, ?_, ?_⟩
    · rw [Nat.cast_ofNat]
      field_simp
      ring
    · calc
        x * (-x / 2) ^ 2 = x ^ 3 / 4 := by
          rw [div_pow, ← mul_div_assoc]
          congr 1 <;> ring
        _ = 1 := by rw [hx3, div_self hfour]

end MetaMathlibExt
