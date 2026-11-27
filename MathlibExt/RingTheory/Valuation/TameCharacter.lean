/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_GaloisRep_TameCharacter.lean`,
`Theorems/Thm_ValuationSubring_tameCharacter_eq_of_div_mem_of_div_mem.lean`,
`P2M/Sol/S_ValuationSubring_tameCharacter_eq_of_div_mem_of_div_mem.lean`,
`Theorems/Thm_ValuationSubring_exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_
inertiaSubgroupIn.lean`, and
`P2M/Sol/S_ValuationSubring_exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_
inertiaSubgroupIn.lean`
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

public import Mathlib.RingTheory.Valuation.RamificationGroup
public import MathlibExt.RingTheory.Valuation.InertiaRootsOfUnity
import MathlibExt.NumberTheory.Padics.DecompositionSubgroup

/-!
# The tame character of a valuation subring

For a valuation subring `P` of a field `L`, an element `π` and a `K`-algebra automorphism `σ` of
`L`, the tame character `P.tameCharacter π σ` is the residue of `σ π / π` when this ratio lies in
`P` (and `0` otherwise). When `L` is algebraic over `K`, on the inertia subgroup it does not depend
on `π` up to units of `P`, and every unit of `P` has trivial tame character.
-/

@[expose] public section

open scoped Pointwise

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The tame character attached to `π`: the residue of `σ π / π` in the residue field of `P`
when `σ π / π ∈ P`, and `0` otherwise. -/
noncomputable def tameCharacter (P : ValuationSubring L) (π : L) (σ : L ≃ₐ[K] L) :
    IsLocalRing.ResidueField P := by
  classical
  exact if h : σ π / π ∈ P then IsLocalRing.residue P ⟨σ π / π, h⟩ else 0

variable (P : ValuationSubring L)

theorem tameCharacter_of_mem (π : L) (σ : L ≃ₐ[K] L) (h : σ π / π ∈ P) :
    P.tameCharacter π σ = IsLocalRing.residue P ⟨σ π / π, h⟩ := by
  unfold ValuationSubring.tameCharacter
  simp [h]

private theorem apply_mem_of_mem_decompositionSubgroup' {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ P.decompositionSubgroup K) {x : L} (hx : x ∈ P) : σ x ∈ P := by
  have h : σ • P = P := MulAction.mem_stabilizer_iff.mp hσ
  have hmem : σ • x ∈ ((σ • P : ValuationSubring L) : Set L) := by
    rw [coe_pointwise_smul]
    exact Set.smul_mem_smul_set hx
  rw [h] at hmem
  exact hmem

private theorem mem_decompositionSubgroup_of_mem_inertiaSubgroupIn {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ P.inertiaSubgroupIn K) : σ ∈ P.decompositionSubgroup K := by
  obtain ⟨σ', _, rfl⟩ := Subgroup.mem_map.mp hσ
  exact σ'.2

private theorem residue_apply_eq_of_mem_inertiaSubgroupIn {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ P.inertiaSubgroupIn K) {x : L} (hx : x ∈ P) (hσx : σ x ∈ P) :
    IsLocalRing.residue P ⟨σ x, hσx⟩ = IsLocalRing.residue P ⟨x, hx⟩ := by
  obtain ⟨σ', hσ', rfl⟩ := Subgroup.mem_map.mp hσ
  have hker : MulSemiringAction.toRingAut (P.decompositionSubgroup K)
      (IsLocalRing.ResidueField P) σ' = 1 :=
    (MonoidHom.mem_ker).mp hσ'
  have h1 : (MulSemiringAction.toRingAut (P.decompositionSubgroup K)
      (IsLocalRing.ResidueField P) σ') (IsLocalRing.residue P ⟨x, hx⟩) =
      IsLocalRing.residue P ⟨x, hx⟩ := by
    rw [hker]
    rfl
  have h2 : IsLocalRing.residue P (σ' • (⟨x, hx⟩ : P)) = IsLocalRing.residue P ⟨x, hx⟩ := h1
  have hact : (σ' • (⟨x, hx⟩ : P) : P) =
      ⟨(P.decompositionSubgroup K).subtype σ' x, hσx⟩ := Subtype.ext rfl
  rw [hact] at h2
  exact h2

private theorem apply_div_mem_of_mem_decompositionSubgroup [Algebra.IsAlgebraic K L]
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ P.decompositionSubgroup K) {x : L} (hx : x ≠ 0) :
    σ x / x ∈ P ∧ x / σ x ∈ P := by
  have hv := P.valuation_map_eq_of_mem_decompositionSubgroup hσ x
  have hx' : P.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  refine ⟨(P.valuation_le_one_iff _).mp (le_of_eq ?_),
    (P.valuation_le_one_iff _).mp (le_of_eq ?_)⟩
  · rw [map_div₀, hv, div_self hx']
  · rw [map_div₀, hv, div_self hx']

/-- If `L` is algebraic over `K`, then on the inertia subgroup the tame character does not change
when `π` is replaced by `π'` with `π' / π` a unit of `P`. -/
theorem tameCharacter_eq_of_div_mem_of_div_mem [Algebra.IsAlgebraic K L] (π π' : L) (hπ : π ≠ 0)
    (hπ' : π' ≠ 0) (hu : π' / π ∈ P) (hu' : π / π' ∈ P)
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ P.inertiaSubgroupIn K) :
    P.tameCharacter π' σ = P.tameCharacter π σ := by
  have hσD : σ ∈ P.decompositionSubgroup K :=
    mem_decompositionSubgroup_of_mem_inertiaSubgroupIn P hσ
  have hσπ : σ π / π ∈ P := (apply_div_mem_of_mem_decompositionSubgroup P hσD hπ).1
  have hσu : σ (π' / π) ∈ P := apply_mem_of_mem_decompositionSubgroup' P hσD hu
  have hσπ0 : σ π ≠ 0 := (map_ne_zero σ).mpr hπ
  have hcoc : σ π' / π' = (σ (π' / π) * (π / π')) * (σ π / π) := by
    rw [map_div₀]
    field_simp
  have hmem : σ π' / π' ∈ P := by
    rw [hcoc]
    exact MulMemClass.mul_mem (MulMemClass.mul_mem hσu hu') hσπ
  rw [tameCharacter_of_mem P π' σ hmem, tameCharacter_of_mem P π σ hσπ]
  have hprod : (⟨σ π' / π', hmem⟩ : P) =
      (⟨σ (π' / π), hσu⟩ * ⟨π / π', hu'⟩) * ⟨σ π / π, hσπ⟩ :=
    Subtype.ext (by simpa only [MulMemClass.coe_mul] using hcoc)
  rw [hprod, map_mul, map_mul, residue_apply_eq_of_mem_inertiaSubgroupIn P hσ hu hσu,
    ← map_mul]
  have hone : (⟨π' / π, hu⟩ : P) * ⟨π / π', hu'⟩ = 1 := Subtype.ext (by
    change π' / π * (π / π') = 1
    rw [div_mul_div_comm, mul_comm π' π, div_self (mul_ne_zero hπ hπ')])
  rw [hone, map_one, one_mul]

private theorem tameCharacter_one (σ : L ≃ₐ[K] L) : P.tameCharacter 1 σ = 1 := by
  have h : σ 1 / 1 ∈ P := by rw [map_one, div_one]; exact one_mem P
  rw [tameCharacter_of_mem P 1 σ h]
  have h1 : (⟨σ 1 / 1, h⟩ : ↥P) = 1 := Subtype.ext (by simp)
  rw [h1, map_one]

/-- If `L` is algebraic over `K` and `σ` lies in the inertia subgroup, every nonzero `z` satisfies
`σ z = a * z` for a unit `a` of `P` whose residue is the tame character of `z`, and units of `P`
have trivial tame character. -/
theorem exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn
    [Algebra.IsAlgebraic K L] {σ : L ≃ₐ[K] L} (hσ : σ ∈ P.inertiaSubgroupIn K) :
    (∀ z : L, z ≠ 0 →
      ∃ a : (↥P)ˣ, ((a : ↥P) : L) * z = σ z ∧
        IsLocalRing.residue (↥P) (a : ↥P) = P.tameCharacter z σ) ∧
    ∀ u : (↥P)ˣ, P.tameCharacter ((u : ↥P) : L) σ = 1 := by
  have hd : σ ∈ P.decompositionSubgroup K :=
    mem_decompositionSubgroup_of_mem_inertiaSubgroupIn P hσ
  refine ⟨fun z hz => ?_, fun u => ?_⟩
  · have hσz : σ z ≠ 0 := (map_ne_zero σ).mpr hz
    obtain ⟨hmem, hmem'⟩ := apply_div_mem_of_mem_decompositionSubgroup P hd hz
    let a : (↥P)ˣ :=
      ⟨⟨σ z / z, hmem⟩, ⟨z / σ z, hmem'⟩,
        Subtype.ext (show σ z / z * (z / σ z) = 1 by
          rw [div_mul_div_comm, mul_comm z (σ z), div_self (mul_ne_zero hσz hz)]),
        Subtype.ext (show z / σ z * (σ z / z) = 1 by
          rw [div_mul_div_comm, mul_comm (σ z) z, div_self (mul_ne_zero hz hσz)])⟩
    refine ⟨a, ?_, ?_⟩
    · change σ z / z * z = σ z
      exact div_mul_cancel₀ (σ z) hz
    · rw [tameCharacter_of_mem P z σ hmem]
  · have hvu : P.valuation ((u : ↥P) : L) = 1 := P.valuation_unit u
    have hu0 : ((u : ↥P) : L) ≠ 0 :=
      (Valuation.ne_zero_iff _).mp (by rw [hvu]; exact one_ne_zero)
    have hu : ((u : ↥P) : L) / 1 ∈ P := by rw [div_one]; exact (u : ↥P).2
    have hu' : 1 / ((u : ↥P) : L) ∈ P :=
      (P.valuation_le_one_iff _).mp (by rw [map_div₀, map_one, hvu, div_one])
    rw [tameCharacter_eq_of_div_mem_of_div_mem P 1 ((u : ↥P) : L) one_ne_zero hu0 hu hu' hσ]
    exact tameCharacter_one P σ

end ValuationSubring
