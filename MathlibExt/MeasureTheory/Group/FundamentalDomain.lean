/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives.lean`
and
`P2M/Sol/S_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Action

/-!
# Fundamental domains for subgroups of finite index

If `Γ₂ ≤ Γ₁` and `R` picks one representative of each left coset of `Γ₂`
in `Γ₁`, the union of the `R i`-translates of a fundamental domain for `Γ₁`
is a fundamental domain for `Γ₂`.
-/

@[expose] public section

open MeasureTheory
open scoped Pointwise ENNReal

private theorem subgroup_smul_set {G X : Type*} [Group G] [MulAction G X]
    (Γ : Subgroup G) (γ : Γ) (s : Set X) : γ • s = (γ : G) • s := rfl

private theorem smul_iUnion_inv_smul {G X ι : Type*} [Group G] [MulAction G X]
    (Γ : Subgroup G) (R : ι → Γ) (g : G) (s : Set X) :
    g • (⋃ i, ((R i : G)⁻¹) • s) = ⋃ i, (g * (R i : G)⁻¹) • s := by
  rw [Set.smul_set_iUnion]
  refine Set.iUnion_congr fun i => ?_
  rw [smul_smul]

/-- From a fundamental domain for `Γ₁`, a union of coset-representative
translates gives a fundamental domain for a subgroup `Γ₂ ≤ Γ₁`. -/
theorem MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives
    {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (Γ₁ Γ₂ : Subgroup G) (hle : Γ₂ ≤ Γ₁) [Countable Γ₁]
    [MeasurableSpace G] [MeasurableSMul G X] [SMulInvariantMeasure G X μ]
    (𝓕 : Set X) (h𝓕 : IsFundamentalDomain Γ₁ 𝓕 μ)
    (R : ι → Γ₁) (hR : ∀ γ : Γ₁, ∃! i, ((R i)⁻¹ * γ : G) ∈ Γ₂) :
    IsFundamentalDomain Γ₂ (⋃ i, ((R i : G)⁻¹) • 𝓕) μ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · refine NullMeasurableSet.iUnion fun i => ?_
    have h := h𝓕.nullMeasurableSet_smul (R i)⁻¹
    rwa [subgroup_smul_set, Subgroup.coe_inv] at h
  · filter_upwards [h𝓕.ae_covers] with x hx
    obtain ⟨γ, hγ⟩ := hx
    obtain ⟨i, hi, -⟩ := hR γ
    refine ⟨⟨(R i : G)⁻¹ * γ, hi⟩, ?_⟩
    rw [Subgroup.smul_def]
    change ((R i : G)⁻¹ * (γ : G)) • x ∈ ⋃ i, ((R i : G)⁻¹) • 𝓕
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [mul_smul]
    exact Set.smul_mem_smul_set (by rw [← Subgroup.smul_def]; exact hγ)
  · intro γ γ' hne
    change AEDisjoint μ (γ • ⋃ i, ((R i : G)⁻¹) • 𝓕) (γ' • ⋃ i, ((R i : G)⁻¹) • 𝓕)
    rw [subgroup_smul_set, subgroup_smul_set, smul_iUnion_inv_smul Γ₁ R,
      smul_iUnion_inv_smul Γ₁ R, AEDisjoint.iUnion_left_iff]
    intro i
    rw [AEDisjoint.iUnion_right_iff]
    intro j
    have hγ₁ : ((γ : G) * (R i : G)⁻¹) ∈ Γ₁ := mul_mem (hle γ.2) (inv_mem (R i).2)
    have hγ₁' : ((γ' : G) * (R j : G)⁻¹) ∈ Γ₁ := mul_mem (hle γ'.2) (inv_mem (R j).2)
    have hne' : (⟨(γ : G) * (R i : G)⁻¹, hγ₁⟩ : Γ₁) ≠ ⟨(γ' : G) * (R j : G)⁻¹, hγ₁'⟩ := by
      intro heq
      have heq' : (γ : G) * (R i : G)⁻¹ = (γ' : G) * (R j : G)⁻¹ :=
        congrArg Subtype.val heq
      have hmem : ((R j)⁻¹ * R i : G) ∈ Γ₂ := by
        have hthis : ((R j : G)⁻¹ * (R i : G)) = (γ' : G)⁻¹ * (γ : G) := by
          calc ((R j : G)⁻¹ * (R i : G))
              = (γ' : G)⁻¹ * ((γ' : G) * (R j : G)⁻¹) * (R i : G) := by group
            _ = (γ' : G)⁻¹ * ((γ : G) * (R i : G)⁻¹) * (R i : G) := by rw [heq']
            _ = (γ' : G)⁻¹ * (γ : G) := by group
        rw [Subgroup.coe_inv, hthis]
        exact mul_mem (inv_mem γ'.2) γ.2
      have hii : ((R i)⁻¹ * R i : G) ∈ Γ₂ := by
        rw [Subgroup.coe_inv, inv_mul_cancel]; exact one_mem _
      obtain ⟨k, -, hk⟩ := hR (R i)
      have hij : i = j := (hk i hii).trans (hk j hmem).symm
      subst hij
      apply hne
      apply Subtype.ext
      exact mul_right_cancel heq'
    have h := h𝓕.aedisjoint hne'
    simpa only [Function.onFun, subgroup_smul_set] using h
