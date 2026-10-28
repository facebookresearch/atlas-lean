/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedSubgroups

/-! The coverage implication needed by the Höhn--Seysen axis certificates
(arXiv:2508.01037, Sections 3.1--3.2).

An explicit finite list of local orbit representatives describes the full
generated orbit once its union contains the starting axis, is invariant under
triality, and each representative belongs to the generated orbit. The triality
invariance hypothesis is the mathematical obligation of the certificate checker;
no unchecked numerical or modular certificate is asserted to satisfy it here. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A union of actual local H-orbits of specified vectors. -/
noncomputable def generatedLocalOrbitUnion {ι : Type*} (v : ι → GriessSpace) :
    Set GriessSpace := {x | ∃ i h, rhoLocal h (v i) = x}

/-- The actual orbit of a specified vector under the named generated group. -/
noncomputable def generatedVectorOrbit (a : GriessSpace) : Set GriessSpace :=
  {x | ∃ g : G, g.val a = x}

theorem generatedLocalOrbitUnion_local {ι : Type*} (v : ι → GriessSpace)
    (h : H) : Set.MapsTo (rhoLocal h) (generatedLocalOrbitUnion v)
      (generatedLocalOrbitUnion v) := by
  rintro x ⟨i, k, rfl⟩
  exact ⟨i, h * k, by rw [map_mul, LinearEquiv.mul_apply]⟩

/-- The double-coset reduction used by an axis certificate. The subgroup N
must genuinely be normalized by triality in the local action; the subgroup C
must genuinely fix the relevant axis. A verified N--C decomposition of every
local element then reduces triality coverage to the listed representatives. -/
theorem generatedLocalOrbitUnion_triality_of_double_cosets {ι κ : Type*}
    (v : ι → GriessSpace) (N : Subgroup H) (C : ι → Subgroup H)
    (r : ι → κ → H)
    (hfix : ∀ i c, c ∈ C i → rhoLocal c (v i) = v i)
    (hnormalize : ∀ n, n ∈ N → ∃ n' : H,
      sExtra * rhoLocal n = rhoLocal n' * sExtra)
    (hcover : ∀ i h, ∃ j n c, n ∈ N ∧ c ∈ C i ∧ h = n * r i j * c)
    (htransition : ∀ i j,
      sExtra (rhoLocal (r i j) (v i)) ∈ generatedLocalOrbitUnion v) :
    Set.MapsTo sExtra (generatedLocalOrbitUnion v) (generatedLocalOrbitUnion v) := by
  rintro x ⟨i, h, rfl⟩
  obtain ⟨j, n, c, hn, hc, rfl⟩ := hcover i h
  obtain ⟨n', he⟩ := hnormalize n hn
  have he' := LinearEquiv.congr_fun he (rhoLocal (r i j) (v i))
  simp only [LinearEquiv.mul_apply] at he'
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix i c hc, he']
  exact generatedLocalOrbitUnion_local v n' (htransition i j)

/-- Local and triality invariance propagate to every element of the actual G. -/
theorem generatedLocalOrbitUnion_generated {ι : Type*} (v : ι → GriessSpace)
    (htriality : Set.MapsTo sExtra (generatedLocalOrbitUnion v)
      (generatedLocalOrbitUnion v)) (g : G) :
    Set.MapsTo g.val (generatedLocalOrbitUnion v) (generatedLocalOrbitUnion v) := by
  let U := generatedLocalOrbitUnion v
  let K : Subgroup (GriessSpace ≃ₗ[ℝ] GriessSpace) :=
    { carrier := {f | Set.MapsTo f U U ∧
        Set.MapsTo (f⁻¹ : GriessSpace ≃ₗ[ℝ] GriessSpace) U U}
      one_mem' := ⟨fun _ hx => hx, fun _ hx => hx⟩
      mul_mem' := by
        intro a b ha hb
        refine ⟨ha.1.comp hb.1, ?_⟩
        intro x hx
        rw [mul_inv_rev, LinearEquiv.mul_apply]
        exact hb.2 (ha.2 hx)
      inv_mem' := fun ha => ⟨ha.2, by simpa only [inv_inv] using ha.1⟩ }
  have hlocal (h : H) : rhoLocal h ∈ K := by
    exact ⟨generatedLocalOrbitUnion_local v h,
      by simpa only [map_inv] using generatedLocalOrbitUnion_local v h⁻¹⟩
  have hextra : sExtra ∈ K := by
    refine ⟨htriality, ?_⟩
    intro x hx
    have he : sExtra⁻¹ x = sExtra (sExtra x) := by
      apply sExtra.injective
      change sExtra (sExtra.symm x) = sExtra (sExtra (sExtra x))
      rw [LinearEquiv.apply_symm_apply, sExtra_triple]
    rw [he]
    exact htriality (htriality hx)
  have hGK : G ≤ K := by
    apply (Subgroup.closure_le _).mpr
    rintro f (⟨h, rfl⟩ | hf)
    · exact hlocal h
    · exact Set.mem_singleton_iff.mp hf ▸ hextra
  exact (hGK g.property).1

/-- A source-bound certificate establishing triality coverage suffices to
identify the local orbit union with the genuine generated orbit. -/
theorem generatedVectorOrbit_eq_localOrbitUnion {ι : Type*}
    (v : ι → GriessSpace) (a : GriessSpace)
    (ha : a ∈ generatedLocalOrbitUnion v)
    (hv : ∀ i, v i ∈ generatedVectorOrbit a)
    (htriality : Set.MapsTo sExtra (generatedLocalOrbitUnion v)
      (generatedLocalOrbitUnion v)) :
    generatedVectorOrbit a = generatedLocalOrbitUnion v := by
  apply Set.Subset.antisymm
  · rintro x ⟨g, rfl⟩
    exact generatedLocalOrbitUnion_generated v htriality g ha
  · rintro x ⟨i, h, rfl⟩
    obtain ⟨g, hg⟩ := hv i
    refine ⟨localIntoGenerated h * g, ?_⟩
    change rhoLocal h (g.val a) = rhoLocal h (v i)
    rw [hg]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
