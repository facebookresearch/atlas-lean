/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDiscreteValuationRing_algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible.lean`,
`Definitions/Def_GaloisRep_Flat.lean`
and
`P2M/Sol/S_IsDiscreteValuationRing_algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Rationals localized at a prime, as a subring of `ℚ`

`Rat.localizedAt p` is the subring of `ℚ` consisting of the rationals whose
denominator (in lowest terms) is coprime to `p`. When `R` is a discrete
valuation ring with fraction field `ℚ` and the rational prime `p` remains
irreducible in `R`, the image of `R` in `ℚ` is exactly this subring.
-/

@[expose] public section

namespace Rat

/-- The subring of `ℚ` of rationals whose denominator is coprime to `p`:
the localization of `ℤ` at the prime `p`, viewed inside `ℚ`. -/
public def localizedAt (p : ℕ) : Subring ℚ where
  carrier := {q : ℚ | q.den.Coprime p}
  mul_mem' {a b} ha hb :=
    (Nat.coprime_mul_iff_left.mpr ⟨ha, hb⟩).of_dvd_left (Rat.mul_den_dvd a b)
  one_mem' := by simp
  add_mem' {a b} ha hb :=
    (Nat.coprime_mul_iff_left.mpr ⟨ha, hb⟩).of_dvd_left (Rat.add_den_dvd a b)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

/-- Membership in `Rat.localizedAt p` is coprimality of the denominator. -/
public theorem mem_localizedAt {p : ℕ} {q : ℚ} :
    q ∈ localizedAt p ↔ q.den.Coprime p := Iff.rfl

end Rat

namespace IsDiscreteValuationRing

/-- The image of a discrete valuation ring `R` with fraction field `ℚ` in
`ℚ` is the subring of rationals whose denominator is coprime to `p`,
provided the rational prime `p` is irreducible in `R`. -/
public theorem algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (p : ℕ) [Fact p.Prime] (hp : Irreducible (p : R)) :
    (algebraMap R ℚ).range = Rat.localizedAt p := by
  have hinj : Function.Injective (algebraMap R ℚ) := IsFractionRing.injective R ℚ
  have hp_not_unit : ¬ IsUnit (p : R) := hp.not_isUnit
  have hintR : ∀ n : ℤ, algebraMap R ℚ (n : R) = (n : ℚ) := fun n =>
    map_intCast (algebraMap R ℚ) n
  have hnatR : ∀ n : ℕ, algebraMap R ℚ (n : R) = (n : ℚ) := fun n =>
    map_natCast (algebraMap R ℚ) n
  have unit_of_coprime : ∀ n : ℕ, n.Coprime p → IsUnit (n : R) := by
    intro n hcop
    have h1 : IsCoprime (n : ℤ) (p : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast hcop)
    obtain ⟨u, v, huv⟩ := h1
    have hR : (u : R) * (n : R) + (v : R) * (p : R) = 1 := by
      have h := congrArg (fun z : ℤ => (z : R)) huv
      push_cast at h; exact_mod_cast h
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hR with h | h
    · exact isUnit_of_mul_isUnit_right h
    · exact absurd (isUnit_of_mul_isUnit_right h) hp_not_unit
  have den_mul : ∀ q : ℚ, (q.den : ℚ) * q = (q.num : ℚ) := fun q => by
    have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
    rw [mul_comm, ← eq_div_iff hd]; exact (Rat.num_div_den q).symm
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    set q := algebraMap R ℚ r with hq_def
    rw [Rat.mem_localizedAt]
    by_contra hden
    have hpd : p ∣ q.den :=
      ((Fact.out : p.Prime).dvd_iff_not_coprime).mpr (fun h => hden h.symm)
    have hbr : (q.den : R) * r = (q.num : R) := by
      apply hinj
      rw [map_mul, hnatR, hintR, ← hq_def]
      exact den_mul q
    have hcop : IsCoprime (q.num : ℤ) (q.den : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast q.reduced)
    obtain ⟨x, y, hxy⟩ := hcop
    have hxyR : (x : R) * (q.num : R) + (y : R) * (q.den : R) = 1 := by
      have h := congrArg (fun z : ℤ => (z : R)) hxy
      push_cast at h; exact_mod_cast h
    have hone : (q.den : R) * ((x : R) * r + (y : R)) = 1 := by
      rw [mul_add, ← mul_assoc, mul_comm (q.den : R) (x : R), mul_assoc, hbr]
      linear_combination hxyR
    have hden_unit : IsUnit (q.den : R) :=
      ⟨⟨_, _, hone, by rw [mul_comm]; exact hone⟩, rfl⟩
    obtain ⟨k, hk⟩ := hpd
    have : IsUnit (p : R) := by
      have hden_eq : (q.den : R) = (p : R) * (k : R) := by
        rw [hk]; push_cast; ring
      rw [hden_eq] at hden_unit
      exact isUnit_of_mul_isUnit_left hden_unit
    exact hp_not_unit this
  · intro q hq
    obtain ⟨u, hu⟩ := unit_of_coprime q.den hq
    refine ⟨(q.num : R) * (↑u⁻¹ : R), ?_⟩
    have huq : algebraMap R ℚ (↑u : R) = (q.den : ℚ) := by rw [hu]; exact hnatR q.den
    have huinv : algebraMap R ℚ (↑u⁻¹ : R) * (q.den : ℚ) = 1 := by
      rw [← huq, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
    rw [map_mul, hintR]
    have h1 : algebraMap R ℚ (↑u⁻¹ : R) = (q.den : ℚ)⁻¹ :=
      (eq_inv_of_mul_eq_one_left huinv)
    rw [h1, ← div_eq_mul_inv]
    exact Rat.num_div_den q

end IsDiscreteValuationRing
