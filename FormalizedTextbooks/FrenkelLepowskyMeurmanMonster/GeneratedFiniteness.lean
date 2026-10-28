/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Applying the analytic finiteness mechanism to the actual Euclidean Griess group.
Triality product preservation is an explicit input to this analytic mechanism.
Milestones instantiates it with the full coordinate proof; finite group or finite
orbit is never assumed.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GriessNorm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.AxialFiniteness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalProductInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.AxialSpectrum
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.AxialSpan

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The source triality belongs to the actual subgroup generated in the milestones. -/
theorem sExtra_mem_G : sExtra ∈ G := by
  apply Subgroup.subset_closure
  exact Or.inr (Set.mem_singleton sExtra)

/-- Extend local product invariance to the generated group using the extra
triality product law. -/
theorem generated_group_preserves_griessProduct
    (htriality : ∀ x y, sExtra (griessProd x y) = griessProd (sExtra x) (sExtra y))
    (g : G) (x y : GriessSpace) : g.val (griessProd x y) = griessProd (g.val x) (g.val y) := by
  have hlocal : ∀ h : H, IsGriessAuto (rhoLocal h) :=
    fun h => ⟨rhoLocal_product h, rhoLocal_form h⟩
  have hextra : IsGriessAuto sExtra := ⟨htriality, sExtra_preserves_griessForm⟩
  exact (G_le_griessAutSubgroup_of_generator_invariance hlocal hextra g.property).1 x y

/-- The actual Euclidean generated group preserves its actual continuous
product given the triality product law. -/
theorem griessEuclideanGeneratedGroup_product
    (htriality : ∀ x y, sExtra (griessProd x y) = griessProd (sExtra x) (sExtra y))
    (g : griessEuclideanGeneratedGroup) (x y : GriessEuclidean) :
    g.val (griessEuclideanProduct x y) = griessEuclideanProduct (g.val x) (g.val y) := by
  obtain ⟨h, hh⟩ := g.property
  change griessEuclideanGroupAction h = g.val at hh
  rw [← hh]
  exact griessEuclideanTransport_product h.val
    (generated_group_preserves_griessProduct htriality h) x y

/-- Canonical finite labels for the signed-short axes. -/
abbrev GriessShortAxisIndex := GriessShortIndex × ZMod 2

/-- The actual Euclidean source axes used in the finite-family criterion. -/
noncomputable def griessSourceAxisFamily (i : GriessShortAxisIndex) : GriessEuclidean :=
  griessEuclideanShortAxis i.1 i.2

/-- The invariant union of actual orbits, without any transitivity identification. -/
noncomputable def griessSourceAxisOrbits : Set GriessEuclidean :=
  ⋃ i : GriessShortAxisIndex,
    algebraAxisOrbit griessEuclideanGeneratedGroup (griessSourceAxisFamily i)

/-- Every source axis lies in its actual orbit union. -/
theorem griessSourceAxisFamily_mem_orbits (i : GriessShortAxisIndex) :
    griessSourceAxisFamily i ∈ griessSourceAxisOrbits := by
  apply Set.mem_iUnion.mpr
  refine ⟨i, 1, ?_⟩
  rfl

/-- The orbit union is invariant under the actual Euclidean generated group. -/
theorem griessSourceAxisOrbits_invariant (g : griessEuclideanGeneratedGroup)
    (x : GriessEuclidean) (hx : x ∈ griessSourceAxisOrbits) : g.val x ∈ griessSourceAxisOrbits := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨h, hh⟩ := hi
  apply Set.mem_iUnion.mpr
  refine ⟨i, g * h, ?_⟩
  change h.val (griessSourceAxisFamily i) = x at hh
  change g.val (h.val (griessSourceAxisFamily i)) = g.val x
  rw [hh]

/-- The actual extra triality acts on the Euclidean orbit union. -/
theorem griessSourceAxisOrbits_triality (x : GriessEuclidean)
    (hx : x ∈ griessSourceAxisOrbits) :
    griessEuclideanTransport sExtra x ∈ griessSourceAxisOrbits := by
  let g : G := ⟨sExtra, sExtra_mem_G⟩
  let h : griessEuclideanGeneratedGroup :=
    ⟨griessEuclideanGroupAction g, ⟨g, rfl⟩⟩
  exact griessSourceAxisOrbits_invariant h x hx

/-- The concrete spectral calculation excludes 32 as an eigenvalue,
so the continuous linearized equation has trivial kernel. -/
theorem griessShortAxisLinearization_eq_zero (r : GriessShortIndex) (c : ZMod 2)
    (x : GriessEuclidean) (hx : griessShortAxisLinearization r c x = 0) : x = 0 := by
  rw [griessShortAxisLinearization_apply] at hx
  have h2 : (2 : ℝ) • (griessEuclideanProduct (griessEuclideanShortAxis r c) x -
      (32 : ℝ) • x) = 0 := by
    calc
      _ = -((64 : ℝ) • x - (2 : ℝ) •
        griessEuclideanProduct (griessEuclideanShortAxis r c) x) := by module
      _ = 0 := by rw [hx, neg_zero]
  have hprod : griessEuclideanProduct (griessEuclideanShortAxis r c) x = (32 : ℝ) • x :=
    sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_left (by norm_num))
  have hsource := congrArg griessEuclideanEquiv.symm hprod
  rw [griessEuclideanProduct_apply, LinearEquiv.symm_apply_apply,
    griessEuclideanShortAxis, LinearEquiv.symm_apply_apply, map_smul] at hsource
  have hz := conwayShortAxis_32_kernel r c (griessEuclideanEquiv.symm x) hsource
  have he := congrArg griessEuclideanEquiv hz
  simpa only [LinearEquiv.apply_symm_apply, map_zero] using he

/-- Finite dimensionality makes the actual injective linearization bijective. -/
theorem griessShortAxisLinearization_bijective (r : GriessShortIndex) (c : ZMod 2) :
    Function.Bijective (griessShortAxisLinearization r c) := by
  have hker : (griessShortAxisLinearization r c).toLinearMap.ker = ⊥ :=
    LinearMap.ker_eq_bot'.mpr (griessShortAxisLinearization_eq_zero r c)
  have hinj := LinearMap.ker_eq_bot.mp hker
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The concrete linearized equation has a genuine continuous inverse,
constructed from the proved complete axis spectral calculation. -/
noncomputable def griessShortAxisLinearizationEquiv (r : GriessShortIndex) (c : ZMod 2) :
    GriessEuclidean ≃L[ℝ] GriessEuclidean :=
  (LinearEquiv.ofBijective (griessShortAxisLinearization r c).toLinearMap
    (griessShortAxisLinearization_bijective r c)).toContinuousLinearEquiv

/-- The spectral inverse's forward map is exactly the linearized source equation. -/
theorem griessShortAxisLinearizationEquiv_apply (r : GriessShortIndex) (c : ZMod 2)
    (x : GriessEuclidean) : griessShortAxisLinearizationEquiv r c x =
      (64 : ℝ) • x - (2 : ℝ) • griessEuclideanProduct (griessEuclideanShortAxis r c) x := by
  change griessShortAxisLinearization r c x = _
  exact griessShortAxisLinearization_apply r c x

set_option backward.isDefEq.respectTransparency false in
/-- The invariant union of signed-short axis orbits spans the whole genuine
Euclidean space. This uses the explicit axis-span calculation, not transitivity. -/
theorem griessSourceAxisOrbits_span : Submodule.span ℝ griessSourceAxisOrbits = ⊤ := by
  let P := Submodule.span ℝ griessSourceAxisOrbits
  let Q := P.comap griessEuclideanEquiv.toLinearMap
  have h0 (r : GriessShortIndex) (c : ZMod 2) : conwayShortAxis r c ∈ Q := by
    exact Submodule.subset_span (griessSourceAxisFamily_mem_orbits (r, c))
  have h1 (r : GriessShortIndex) (c : ZMod 2) : sExtra (conwayShortAxis r c) ∈ Q := by
    apply Submodule.subset_span
    have h := griessSourceAxisOrbits_triality (griessSourceAxisFamily (r, c))
      (griessSourceAxisFamily_mem_orbits (r, c))
    simpa only [griessSourceAxisFamily, griessEuclideanShortAxis,
      griessEuclideanTransport_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.coe_toLinearMap] using h
  have h2 (r : GriessShortIndex) (c : ZMod 2) : sExtra (sExtra (conwayShortAxis r c)) ∈ Q := by
    apply Submodule.subset_span
    have h := griessSourceAxisOrbits_triality
      (griessEuclideanTransport sExtra (griessSourceAxisFamily (r, c)))
      (griessSourceAxisOrbits_triality (griessSourceAxisFamily (r, c))
        (griessSourceAxisFamily_mem_orbits (r, c)))
    simpa only [griessSourceAxisFamily, griessEuclideanShortAxis,
      griessEuclideanTransport_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.coe_toLinearMap] using h
  have hQ := submodule_eq_top_of_axes_and_images Q h0 h1 h2
  apply P.eq_top_iff'.mpr
  intro x
  obtain ⟨y, rfl⟩ := griessEuclideanEquiv.surjective x
  have hy : y ∈ Q := by rw [hQ]; trivial
  exact hy

/-- All geometric, spectral, spanning, and analytic finiteness inputs are
proved for the actual construction. The triality product law is supplied
explicitly here and discharged in Milestones. No group or orbit finiteness is assumed. -/
theorem generated_group_finite_of_triality_product
    (htriality : ∀ x y, sExtra (griessProd x y) = griessProd (sExtra x) (sExtra y)) : Finite G := by
  have hf : Finite griessEuclideanGeneratedGroup :=
    algebra_group_finite_of_proper_axis_family griessEuclideanGeneratedGroup
      griessEuclideanProduct griessEuclideanProduct_comm
      (griessEuclideanGeneratedGroup_product htriality) griessEuclideanGeneratedGroup_norm
      64 griessSourceAxisFamily
      (fun i => griessEuclideanShortAxis_square i.1 i.2)
      (fun i => griessShortAxisLinearizationEquiv i.1 i.2)
      (fun i => griessShortAxisLinearizationEquiv_apply i.1 i.2)
      griessSourceAxisOrbits_span
  let : Finite griessEuclideanGeneratedGroup := hf
  exact generated_group_finite_of_euclidean

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
