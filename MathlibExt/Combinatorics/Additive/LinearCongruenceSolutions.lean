/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Int.ModEq

import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.GCD

/-!
# Solutions of a linear congruence

Bézout's identity gives a solution when the gcd divides the right-hand side.
Cancelling the coefficient shows that the solutions form one residue class
modulo `m / gcd(a, m)`.
-/

namespace MetaMathlibExt

/-- **Solutions of a linear congruence.** Let $a$ and $b$ be integers, let $m$ be a positive
integer, and let $d = \gcd(a, m)$. The congruence $a x \equiv b \pmod{m}$ has an integer
solution if and only if $d \mid b$. If $d \mid b$, then exactly $d$ of the numbers
$x \in \{0, 1, \dots, m - 1\}$ are solutions. Moreover, if $x_0$ is a solution, then an integer
$x$ is a solution if and only if $x \equiv x_0 + u \cdot (m / d) \pmod{m}$ for some integer $u$
with $0 \le u \le d - 1$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 3, quoting a
textbook result ([3]) (`integers-2025-A62-thm-3`). -/
public theorem linear_congruence_solutions (a b : ℤ) (m : ℕ) (hm : 0 < m) :
    ((∃ x : ℤ, a * x ≡ b [ZMOD m]) ↔ (Int.gcd a m : ℤ) ∣ b) ∧
      ((Int.gcd a m : ℤ) ∣ b →
        ((Finset.range m).filter fun x : ℕ => a * x ≡ b [ZMOD m]).card = Int.gcd a m) ∧
      ∀ x₀ : ℤ, a * x₀ ≡ b [ZMOD m] → ∀ x : ℤ,
        (a * x ≡ b [ZMOD m] ↔
          ∃ u : ℕ, u < Int.gcd a m ∧ x ≡ x₀ + u * ((m : ℤ) / Int.gcd a m) [ZMOD m]) := by
  let d := Int.gcd a m
  let s := m / d
  have hm' : 0 < (m : ℤ) := Int.natCast_pos.mpr hm
  have hd : 0 < d := Int.gcd_pos_of_ne_zero_right a hm'.ne'
  have hda : (d : ℤ) ∣ a := Int.gcd_dvd_left a m
  have hdm : (d : ℤ) ∣ (m : ℤ) := Int.gcd_dvd_right a m
  have hds : d * s = m := Nat.mul_div_cancel' (Int.natCast_dvd_natCast.mp hdm)
  have hs : 0 < s :=
    Nat.div_pos (Nat.le_of_dvd hm (Int.natCast_dvd_natCast.mp hdm)) hd
  have hs' : 0 < (s : ℤ) := Int.natCast_pos.mpr hs
  have hds' : (d : ℤ) * s = m := by exact_mod_cast hds
  have hstep : (s : ℤ) = (m : ℤ) / d := Int.natCast_ediv m d
  have h_exists : (∃ x : ℤ, a * x ≡ b [ZMOD m]) ↔ (d : ℤ) ∣ b := by
    constructor
    · rintro ⟨x, hx⟩
      simpa using Int.dvd_add (hdm.trans hx.dvd) (dvd_mul_of_dvd_left hda x)
    · rintro ⟨k, rfl⟩
      refine ⟨Int.gcdA a m * k, Int.modEq_of_dvd ?_⟩
      rw [show (d : ℤ) = _ from Int.gcd_eq_gcd_ab a m, add_mul, mul_assoc, add_sub_cancel_left]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  -- Once a solution is fixed, cancelling `a` reduces the modulus from `m` to `s`.
  have h_period (x₀ : ℤ) (h₀ : a * x₀ ≡ b [ZMOD m]) (x : ℤ) :
      a * x ≡ b [ZMOD m] ↔ x ≡ x₀ [ZMOD s] := by
    constructor
    · intro hx
      simpa only [hstep, Int.gcd_comm (m : ℤ) a] using
        Int.ModEq.cancel_left_div_gcd hm' (hx.trans h₀.symm)
    · intro hx
      have hmul : (m : ℤ) ∣ a * s := by
        obtain ⟨k, hk⟩ := hda
        exact ⟨k, by rw [hk, ← hds']; ac_rfl⟩
      exact (hx.mul_left'.of_dvd hmul).trans h₀
  refine ⟨h_exists, ?_, ?_⟩
  · intro hb
    change _ = d
    obtain ⟨x₀, h₀⟩ := h_exists.mpr hb
    obtain ⟨r, _, hr⟩ := Int.existsUnique_equiv_nat x₀ hs'
    have h_filter :
        ((Finset.range m).filter fun x : ℕ => a * x ≡ b [ZMOD m]) =
          (Finset.range m).filter fun x : ℕ => x ≡ r [MOD s] := by
      refine Finset.filter_congr fun x _ => ?_
      rw [h_period x₀ h₀, ← Int.natCast_modEq_iff]
      exact ⟨fun hx => hx.trans hr.symm, fun hx => hx.trans hr⟩
    rw [h_filter, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card m hs r, ← hds,
      Nat.mul_div_cancel _ hs, Nat.mul_mod_left]
    simp
  · intro x₀ h₀ x
    rw [h_period x₀ h₀, ← hstep]
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := hx.symm.dvd
      have hxk : x = x₀ + k * s := by rw [mul_comm k, ← hk, add_sub_cancel]
      -- Reducing the translation index modulo `d` does not change the class modulo `m`.
      have hd' : 0 < (d : ℤ) := Int.natCast_pos.mpr hd
      have hrem := Int.emod_nonneg k hd'.ne'
      refine ⟨(k % d).toNat, (Int.toNat_lt hrem).mpr (Int.emod_lt_of_pos k hd'), ?_⟩
      rw [Int.toNat_of_nonneg hrem, hxk, ← hds']
      exact ((Int.mod_modEq k d).symm.mul_right').add_left x₀
    · rintro ⟨u, _, hx⟩
      have hsm : (s : ℤ) ∣ m := ⟨d, by rw [mul_comm, hds']⟩
      have hshift : x₀ + (u : ℤ) * s ≡ x₀ [ZMOD s] := by
        rw [mul_comm (u : ℤ)]
        exact Int.modEq_add_fac_self
      exact (hx.of_dvd hsm).trans hshift

end MetaMathlibExt
