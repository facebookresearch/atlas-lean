/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MeasureTheory_exists_measurableSet_isFundamentalDomain_op_
of_discreteTopology.lean`
and
`P2M/Sol/S_MeasureTheory_exists_measurableSet_isFundamentalDomain_op_
of_discreteTopology.lean`
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

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Bases

/-!
# Measurable fundamental domains for discrete subgroups

Every discrete subgroup of a second-countable Hausdorff topological group
admits a measurable fundamental domain for the opposite action, simultaneously
for every measure.
-/

@[expose] public section

namespace FundamentalDomainExistsAux

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A symmetric open neighborhood of `1` on which `w⁻¹ * v` stays in a given
neighborhood of `1`. -/
private theorem exists_open_inv_mul_subset {W : Set G} (hW : W ∈ nhds (1 : G)) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ ∀ v ∈ V, ∀ w ∈ V, w⁻¹ * v ∈ W := by
  obtain ⟨V₁, hV₁o, hV₁1, hV₁⟩ := exists_open_nhds_one_split hW
  refine ⟨V₁ ∩ V₁⁻¹, hV₁o.inter hV₁o.inv, ⟨hV₁1, by simpa using hV₁1⟩, ?_⟩
  rintro v ⟨hv, -⟩ w ⟨-, hw⟩
  exact hV₁ _ (by simpa using hw) _ hv

variable [SecondCountableTopology G]

/-- A set meeting every orbit `x * Γ` exactly once, built as a countable
disjoint union of measurable pieces. -/
private theorem exists_transversal (Γ : Subgroup G) (hΓ : DiscreteTopology Γ) :
    ∃ D : Set G, (∃ (U : ℕ → Set G) (S : ℕ → Set G), (∀ k, IsOpen (U k)) ∧
        (∀ k, IsOpen (S k)) ∧
        D = ⋃ k, (U k ∩ ⋂ j ∈ Finset.range k, (S j)ᶜ)) ∧
      ∀ x : G, ∃! γ : Γ, x * (γ : G) ∈ D := by
  classical
  have h1open : IsOpen ({(1 : Γ)} : Set Γ) := isOpen_discrete _
  obtain ⟨W, hWo, hWΓ⟩ := isOpen_induced_iff.mp h1open
  have h1W : (1 : G) ∈ W := by
    have : (1 : Γ) ∈ (↑) ⁻¹' W := by rw [hWΓ]; exact rfl
    exact this
  have hWuniq : ∀ γ : Γ, (γ : G) ∈ W → γ = 1 := by
    intro γ hγ
    have : γ ∈ (↑) ⁻¹' W := hγ
    rw [hWΓ] at this
    exact this
  obtain ⟨V, hVo, h1V, hV⟩ := exists_open_inv_mul_subset (hWo.mem_nhds h1W)
  obtain ⟨S₀, hS₀c, hS₀d⟩ := TopologicalSpace.exists_countable_dense G
  have hS₀ne : S₀.Nonempty := hS₀d.nonempty
  obtain ⟨xs, hxs⟩ := hS₀c.exists_eq_range hS₀ne
  let U : ℕ → Set G := fun k => (fun v => xs k * v) '' V
  have hUo : ∀ k, IsOpen (U k) := fun k => (Homeomorph.mulLeft (xs k)).isOpenMap _ hVo
  have hUmem : ∀ k p, p ∈ U k ↔ (xs k)⁻¹ * p ∈ V := by
    intro k p
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa using hv
    · intro hp
      exact ⟨(xs k)⁻¹ * p, hp, by group⟩
  have hcover : ∀ g : G, ∃ k, g ∈ U k := by
    intro g
    have hopen : IsOpen ((fun v => g * v⁻¹) '' V) := by
      have : (fun v : G => g * v⁻¹) = (Homeomorph.mulLeft g) ∘ (Homeomorph.inv G) := by
        funext v; rfl
      rw [this, Set.image_comp]
      exact (Homeomorph.mulLeft g).isOpenMap _ ((Homeomorph.inv G).isOpenMap _ hVo)
    have hne : ((fun v => g * v⁻¹) '' V).Nonempty := ⟨g * 1⁻¹, 1, h1V, rfl⟩
    obtain ⟨s, hsS, v, hv, rfl⟩ := hS₀d.exists_mem_open hopen hne
    rw [hxs] at hsS
    obtain ⟨k, hk⟩ := hsS
    refine ⟨k, (hUmem k g).mpr ?_⟩
    rw [hk]
    simpa using hv
  have huniq : ∀ k (y : G) (γ₁ γ₂ : Γ), y * (γ₁ : G) ∈ U k → y * (γ₂ : G) ∈ U k →
      γ₁ = γ₂ := by
    intro k y γ₁ γ₂ h₁ h₂
    rw [hUmem] at h₁ h₂
    have hw := hV _ h₁ _ h₂
    have : ((xs k)⁻¹ * (y * γ₂))⁻¹ * ((xs k)⁻¹ * (y * γ₁)) = ((γ₂⁻¹ * γ₁ : Γ) : G) := by
      push_cast
      group
    rw [this] at hw
    have := hWuniq _ hw
    rw [inv_mul_eq_one] at this
    exact this.symm
  let S : ℕ → Set G := fun j => ⋃ γ : Γ, (fun p : G => p * (γ : G)) ⁻¹' U j
  have hSo : ∀ j, IsOpen (S j) := fun j =>
    isOpen_iUnion fun γ => (hUo j).preimage (continuous_id.mul continuous_const)
  have hSmem : ∀ j p, p ∈ S j ↔ ∃ γ : Γ, p * (γ : G) ∈ U j := by
    intro j p; simp [S]
  let D : Set G := ⋃ k, (U k ∩ ⋂ j ∈ Finset.range k, (S j)ᶜ)
  have hDmem : ∀ p, p ∈ D ↔ ∃ k, p ∈ U k ∧ ∀ j < k, p ∉ S j := by
    intro p
    simp only [D, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range,
      Set.mem_compl_iff]
  refine ⟨D, ⟨U, S, hUo, hSo, rfl⟩, ?_⟩
  intro x
  have hex : ∃ k, ∃ γ : Γ, x * (γ : G) ∈ U k := by
    obtain ⟨k, hk⟩ := hcover x
    exact ⟨k, 1, by simpa using hk⟩
  let k := Nat.find hex
  obtain ⟨γ, hγ⟩ : ∃ γ : Γ, x * (γ : G) ∈ U k := Nat.find_spec hex
  have hmin : ∀ j < k, ∀ γ' : Γ, x * (γ' : G) ∉ U j := by
    intro j hj γ' h
    exact Nat.find_min hex hj ⟨γ', h⟩
  refine ⟨γ, ?_, ?_⟩
  · refine (hDmem _).mpr ⟨k, hγ, fun j hj hS => ?_⟩
    obtain ⟨γ', hγ'⟩ := (hSmem j _).mp hS
    rw [mul_assoc] at hγ'
    exact hmin j hj (γ * γ') (by push_cast; exact hγ')
  · intro γ' hγ'
    obtain ⟨k', hk'U, hk'S⟩ := (hDmem _).mp hγ'
    have hkk' : k ≤ k' := by
      by_contra h
      exact hmin k' (not_le.mp h) γ' hk'U
    have hk'k : k' ≤ k := by
      by_contra h
      apply hk'S k (not_le.mp h)
      refine (hSmem k _).mpr ⟨γ'⁻¹ * γ, ?_⟩
      have : x * (γ' : G) * ((γ'⁻¹ * γ : Γ) : G) = x * (γ : G) := by push_cast; group
      rw [this]; exact hγ
    have hkeq : k' = k := le_antisymm hk'k hkk'
    rw [hkeq] at hk'U
    exact huniq k x γ' γ hk'U hγ

end FundamentalDomainExistsAux

namespace MeasureTheory

/-- Every discrete subgroup of a second-countable Hausdorff topological group
admits a measurable fundamental domain for the opposite action, simultaneously
for every measure. -/
theorem exists_measurableSet_isFundamentalDomain_op_of_discreteTopology
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) (hΓ : DiscreteTopology Γ) :
    ∃ D : Set G, MeasurableSet D ∧ (∀ x : G, ∃! γ : Γ, x * (γ : G) ∈ D) ∧
      ∀ μ : Measure G, IsFundamentalDomain Γ.op D μ := by
  obtain ⟨D, ⟨U, S, hUo, hSo, rfl⟩, hD⟩ :=
    FundamentalDomainExistsAux.exists_transversal Γ hΓ
  have hmeas : MeasurableSet (⋃ k, (U k ∩ ⋂ j ∈ Finset.range k, (S j)ᶜ)) := by
    refine MeasurableSet.iUnion fun k => (hUo k).measurableSet.inter ?_
    exact MeasurableSet.biInter (Finset.range k).countable_toSet fun j _ =>
      (hSo j).measurableSet.compl
  refine ⟨_, hmeas, hD, fun μ => ?_⟩
  refine IsFundamentalDomain.mk' hmeas.nullMeasurableSet fun x => ?_
  obtain ⟨γ, hγ, huniq⟩ := hD x
  refine ⟨⟨MulOpposite.op (γ : G), Subgroup.mem_op.mpr (by exact γ.2)⟩, ?_, ?_⟩
  · change (MulOpposite.op (γ : G)) • x ∈ _
    rw [op_smul_eq_mul]
    exact hγ
  · rintro ⟨g, hg⟩ hgx
    have hmem : MulOpposite.unop g ∈ Γ := Subgroup.mem_op.mp hg
    have hx : x * MulOpposite.unop g ∈ ⋃ k, (U k ∩ ⋂ j ∈ Finset.range k, (S j)ᶜ) := by
      have : g • x = x * MulOpposite.unop g := by
        rw [← MulOpposite.op_unop g, op_smul_eq_mul, MulOpposite.unop_op]
      have hgx' : g • x ∈ ⋃ k, (U k ∩ ⋂ j ∈ Finset.range k, (S j)ᶜ) := hgx
      rwa [this] at hgx'
    have := huniq ⟨MulOpposite.unop g, hmem⟩ hx
    apply Subtype.ext
    change g = MulOpposite.op (γ : G)
    rw [← this]
    simp

end MeasureTheory
