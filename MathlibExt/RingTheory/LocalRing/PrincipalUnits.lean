/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_LocalRing_PrincipalUnits.lean`,
`Theorems/Thm_IsLocalRing_coe_mul_sub_one_sub_mem_maximalIdeal_pow.lean`,
`Theorems/Thm_IsLocalRing_exists_mem_principalUnits_coe_sub_one_eq.lean`,
`Theorems/Thm_IsLocalRing_index_principalUnits_one.lean`,
`Theorems/Thm_IsLocalRing_map_ringEquiv_mem_maximalIdeal_pow_iff.lean`,
`Theorems/Thm_IsLocalRing_map_ringEquiv_mem_principalUnits_iff.lean`,
`Theorems/Thm_IsLocalRing_pow_mem_principalUnits.lean`,
`Theorems/Thm_IsLocalRing_principalUnits_one_eq_ker_map_residue.lean`
and the corresponding `P2M/Sol/S_IsLocalRing_*.lean` files
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

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Principal units in a local ring

The `k`-th principal units of a commutative local ring `R` are the units
congruent to `1` modulo the `k`-th power of the maximal ideal. They form a
decreasing filtration of `Rˣ`: the first level is the kernel of reduction to
the residue field, elements of `𝔪 ^ k` are realized as `u - 1` for a principal
unit of level `k` when `k ≥ 1`, the product error `uv - 1 - ((u - 1) + (v - 1))`
lies in `𝔪 ^ (2k)`, raising to a prime power `p` with `(p) ∈ 𝔪 ^ e` lands in
level `min (p * k) (k + e)`, and ring automorphisms preserve every level.
-/

@[expose] public section

namespace IsLocalRing

/-- The subgroup of principal units of level `k`: units `u` of a local ring
with `u - 1` in the `k`-th power of the maximal ideal. -/
def principalUnits (R : Type*) [CommRing R] [IsLocalRing R] (k : ℕ) :
    Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ maximalIdeal R ^ k}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    have h : ((u * v : Rˣ) : R) - 1 = ((u : R) - 1) * v + ((v : R) - 1) := by
      push_cast; ring
    rw [Set.mem_ofPred_eq, h]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hu) hv
  inv_mem' := by
    intro u hu
    have h : ((u⁻¹ : Rˣ) : R) - 1 = -(((u⁻¹ : Rˣ) : R) * ((u : R) - 1)) := by
      rw [mul_sub, mul_one, Units.inv_mul, neg_sub]
    rw [Set.mem_ofPred_eq, h]
    exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ hu)

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A unit is a principal unit of level `k` iff `u - 1 ∈ 𝔪 ^ k`. -/
theorem mem_principalUnits_iff {k : ℕ} {u : Rˣ} :
    u ∈ principalUnits R k ↔ (u : R) - 1 ∈ maximalIdeal R ^ k :=
  Iff.rfl

@[simp] theorem principalUnits_zero : principalUnits R 0 = ⊤ := by
  ext u; simp [mem_principalUnits_iff]

/-- The principal-unit filtration is decreasing in the level. -/
theorem principalUnits_antitone : Antitone (principalUnits R) :=
  fun _ _ hkl _ hu => Ideal.pow_le_pow_right hkl hu

/-- For principal units `u, v` of level `k`, the product error
`(u * v) - 1 - ((u - 1) + (v - 1))` lies in `𝔪 ^ (2 * k)`. -/
theorem coe_mul_sub_one_sub_mem_maximalIdeal_pow
    {k : ℕ} {u v : Rˣ} (hu : u ∈ principalUnits R k)
    (hv : v ∈ principalUnits R k) :
    ((u * v : Rˣ) : R) - 1 - (((u : R) - 1) + ((v : R) - 1)) ∈
      maximalIdeal R ^ (2 * k) := by
  have h : ((u * v : Rˣ) : R) - 1 - (((u : R) - 1) + ((v : R) - 1)) =
      ((u : R) - 1) * ((v : R) - 1) := by
    push_cast; ring
  rw [h, two_mul, pow_add]
  exact Ideal.mul_mem_mul hu hv

/-- Every element of `𝔪 ^ k`, for `k ≥ 1`, is `u - 1` for some principal
unit `u` of level `k`. -/
theorem exists_mem_principalUnits_coe_sub_one_eq
    {k : ℕ} (hk : 1 ≤ k) {x : R} (hx : x ∈ maximalIdeal R ^ k) :
    ∃ u ∈ principalUnits R k, (u : R) - 1 = x := by
  have hx1 : x ∈ maximalIdeal R := Ideal.pow_le_self (by omega) hx
  have hunit : IsUnit (1 + x) := by
    have h := isUnit_one_sub_self_of_mem_nonunits (-x)
      ((maximalIdeal R).neg_mem hx1)
    rwa [sub_neg_eq_add] at h
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [mem_principalUnits_iff, IsUnit.unit_spec, add_sub_cancel_left]
    exact hx
  · rw [IsUnit.unit_spec, add_sub_cancel_left]

/-- The principal units of level `1` are the kernel of reduction of units
to the residue field. -/
theorem principalUnits_one_eq_ker_map_residue :
    principalUnits R 1 =
      (Units.map (residue R : R →* ResidueField R)).ker := by
  ext u
  rw [mem_principalUnits_iff, pow_one, MonoidHom.mem_ker, Units.ext_iff,
    Units.coe_map, Units.val_one, MonoidHom.coe_ofClass,
    ← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]

/-- The index of the level-`1` principal units in `Rˣ` is the cardinality
of the unit group of the residue field. -/
theorem index_principalUnits_one :
    (principalUnits R 1).index = Nat.card (ResidueField R)ˣ := by
  have hsurj : Function.Surjective
      (Units.map (residue R : R →* ResidueField R)) :=
    surjective_units_map_of_local_ringHom _ residue_surjective inferInstance
  rw [principalUnits_one_eq_ker_map_residue, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]

/-- A ring automorphism of a local ring preserves membership in every
power of the maximal ideal. -/
theorem map_ringEquiv_mem_maximalIdeal_pow_iff
    (σ : R ≃+* R) {k : ℕ} {x : R} :
    σ x ∈ maximalIdeal R ^ k ↔ x ∈ maximalIdeal R ^ k := by
  have hmap : ∀ (τ : R ≃+* R) {y : R},
      y ∈ maximalIdeal R ^ k → τ y ∈ maximalIdeal R ^ k := by
    intro τ y hy
    have hle : Ideal.map (τ : R →+* R) (maximalIdeal R) ≤
        maximalIdeal R := by
      rw [Ideal.map_le_iff_le_comap]
      intro z hz
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      rw [mem_maximalIdeal, mem_nonunits_iff] at hz
      intro hu
      exact hz (by simpa using hu.map (τ.symm : R →+* R))
    have h1 : τ y ∈ Ideal.map (τ : R →+* R) (maximalIdeal R ^ k) :=
      Ideal.mem_map_of_mem _ hy
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hle k h1
  refine ⟨fun h => ?_, hmap σ⟩
  have h2 := hmap σ.symm h
  rwa [RingEquiv.symm_apply_apply] at h2

/-- A ring automorphism of a local ring preserves the principal-unit
filtration at every level. -/
theorem map_ringEquiv_mem_principalUnits_iff
    (σ : R ≃+* R) {k : ℕ} {u : Rˣ} :
    Units.map (σ : R →* R) u ∈ principalUnits R k ↔
      u ∈ principalUnits R k := by
  have hval : ((Units.map (σ : R →* R) u : Rˣ) : R) - 1 =
      σ ((u : R) - 1) := by
    rw [Units.coe_map, MonoidHom.coe_ofClass, map_sub, map_one]
  rw [mem_principalUnits_iff, mem_principalUnits_iff, hval]
  exact map_ringEquiv_mem_maximalIdeal_pow_iff σ

/-- If `u` is a principal unit of level `k`, `p` is prime, and
`(p : R) ∈ 𝔪 ^ e`, then `u ^ p` is a principal unit of level
`min (p * k) (k + e)`. -/
theorem pow_mem_principalUnits
    {p : ℕ} (hp : p.Prime) {e : ℕ} (hpe : (p : R) ∈ maximalIdeal R ^ e)
    {k : ℕ} {u : Rˣ} (hu : u ∈ principalUnits R k) :
    u ^ p ∈ principalUnits R (min (p * k) (k + e)) := by
  set N := min (p * k) (k + e) with hN
  set x : R := (u : R) - 1 with hx_def
  have hx : x ∈ maximalIdeal R ^ k := hu
  have hxj : ∀ j : ℕ, x ^ j ∈ maximalIdeal R ^ (k * j) := fun j => by
    rw [pow_mul]; exact Ideal.pow_mem_pow hx j
  rw [mem_principalUnits_iff, Units.val_pow_eq_pow_val]
  have hexp : (u : R) ^ p - 1 =
      ∑ j ∈ Finset.range p, x ^ (j + 1) * (p.choose (j + 1) : R) := by
    have hu1 : (u : R) = x + 1 := by rw [hx_def]; ring
    rw [hu1, add_pow, Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right,
      Nat.cast_one, add_sub_cancel_right]
  rw [hexp]
  refine sum_mem fun j hj => ?_
  have hjp : j + 1 ≤ p := Finset.mem_range.mp hj
  rcases lt_or_eq_of_le hjp with hlt | heq
  · obtain ⟨m, hm⟩ := hp.dvd_choose_self (Nat.succ_ne_zero j) hlt
    have hxk : x ^ (j + 1) ∈ maximalIdeal R ^ k :=
      Ideal.pow_le_pow_right (Nat.le_mul_of_pos_right k (Nat.succ_pos j))
        (hxj (j + 1))
    have h1 : x ^ (j + 1) * (p.choose (j + 1) : R) ∈
        maximalIdeal R ^ (k + e) := by
      rw [pow_add, hm, Nat.cast_mul, ← mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hxk hpe)
    exact Ideal.pow_le_pow_right (min_le_right _ _) h1
  · rw [heq, Nat.choose_self, Nat.cast_one, mul_one]
    exact Ideal.pow_le_pow_right
      ((min_le_left _ _).trans_eq (mul_comm p k)) (hxj p)

end IsLocalRing
