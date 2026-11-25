/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

/-!
# A power-of-two divisibility criterion for near-perfect numbers
-/

namespace MetaMathlibExt

/-- **If $b \ge 1$ and $2^b + 1$ divides $3 \cdot 2^a + 1$, then $b = 2$.** Let $a$ and $b$ be
natural numbers with $b \ge 1$. If $2^b + 1$ divides $3 \cdot 2^a + 1$, then $b = 2$.

The source prints the lemma with no range for $b$; its proof divides $a$ by $b$, so $b \ge 1$ is
assumed here. The hypothesis is needed: for $b = 0$, $2^0 + 1 = 2$ divides $3 \cdot 2^0 + 1 = 4$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 10
(`integers-2024-A61-lem-10`). -/
public theorem eq_two_of_two_pow_add_one_dvd {a b : ℕ} (hb : 1 ≤ b)
    (h : 2 ^ b + 1 ∣ 3 * 2 ^ a + 1) : b = 2 := by
  let m : ℕ := 2 ^ b + 1
  let q := a / b
  let r := a % b
  have hr : r < b := Nat.mod_lt _ (by omega)
  have hdecomp : b * q + r = a := Nat.div_add_mod a b
  have hneg : (2 : ZMod m) ^ b = -1 := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      ZMod.natCast_self (2 ^ b + 1)
  have hpow : (2 : ZMod m) ^ a = (-1) ^ q * 2 ^ r := by
    rw [← hdecomp, pow_add, pow_mul, hneg]
  have hzero : (3 : ZMod m) * ((-1) ^ q * 2 ^ r) + 1 = 0 := by
    rw [← hpow]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff _ m).mpr h
  -- Each reduced positive multiple of the modulus is less than twice the modulus.
  have hrpos : 0 < (2 : ℕ) ^ r := Nat.two_pow_pos r
  have hrbound : 2 * 2 ^ r ≤ (2 : ℕ) ^ b := by
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by decide) hr
  rcases Nat.even_or_odd q with hq | hq
  · have heven : (3 : ZMod m) * 2 ^ r + 1 = 0 := by
      simpa only [hq.neg_one_pow, one_mul] using hzero
    have hd : m ∣ 3 * 2 ^ r + 1 := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
        heven
    have heq := Nat.eq_of_dvd_of_lt_two_mul (by omega) hd (by dsimp [m]; omega)
    have hd3 : 3 ∣ (2 : ℕ) ^ b := ⟨2 ^ r, by dsimp [m] at heq; omega⟩
    exact ((by decide : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd3)).elim
  · have hodd : (3 : ZMod m) * 2 ^ r - 1 = 0 := by
      rw [hq.neg_one_pow, neg_one_mul, mul_neg, neg_add_eq_sub, sub_eq_zero] at hzero
      exact sub_eq_zero.mpr hzero.symm
    have hd : m ∣ 3 * 2 ^ r - 1 := (ZMod.natCast_eq_zero_iff _ _).mp (by
      simpa only [Nat.cast_sub (by omega : 1 ≤ 3 * (2 : ℕ) ^ r), Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hodd)
    have heq := Nat.eq_of_dvd_of_lt_two_mul (by omega) hd (by dsimp [m]; omega)
    have hbalance : 3 * (2 : ℕ) ^ r = 2 ^ b + 2 := by dsimp [m] at heq; omega
    have hr0 : r ≠ 0 := by
      intro hr0
      rw [hr0, pow_zero] at hbalance
      omega
    have hb2 : 2 ≤ b := by omega
    have hr1 : r = 1 := by
      by_contra hr1
      have hdiv (k : ℕ) (hk : 2 ≤ k) : 4 ∣ (2 : ℕ) ^ k := Nat.pow_dvd_pow 2 hk
      have hleft := dvd_mul_of_dvd_right (hdiv r (by omega)) 3
      rw [hbalance] at hleft
      exact (by decide : ¬ (4 : ℕ) ∣ 2) ((Nat.dvd_add_right (hdiv b hb2)).mp hleft)
    have hp : (2 : ℕ) ^ b = 2 ^ 2 := by
      rw [hr1] at hbalance
      omega
    exact Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hp

end MetaMathlibExt
