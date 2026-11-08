/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Data.Complex.Basic

import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Algebra.Module.Shrink
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RepresentationTheory.FinGroupCharZero
import MathlibExt.GroupTheory.ClassFunction

@[expose] public section

open CategoryTheory
open scoped MonoidAlgebra
open MathlibExt.GroupTheory.ClassFunctionWanted

noncomputable section

universe u v

namespace FDRep

/-- An irreducible representation gives a simple object of `FDRep`. -/
public theorem simple_of_isIrreducible {k V : Type u} {G : Type v} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] : Simple (FDRep.of ρ) := by
  let F := forget₂ (FDRep k G) (Rep k G)
  constructor
  intro Y f hf
  constructor
  · intro hIso hzero
    have hsurj := (ConcreteCategory.bijective_of_isIso f).2
    have hsimple : IsSimpleModule k[G] ρ.asModule := inferInstance
    have hmodule : Nontrivial ρ.asModule := IsSimpleModule.nontrivial k[G] ρ.asModule
    have hV : Nontrivial V :=
      @Equiv.nontrivial V ρ.asModule ρ.asModuleEquiv.toEquiv.symm hmodule
    obtain ⟨x, hx⟩ := @exists_ne V hV 0
    obtain ⟨y, hy⟩ := hsurj x
    apply hx
    calc
      x = (ConcreteCategory.hom f) y := hy.symm
      _ = (ConcreteCategory.hom (0 : Y ⟶ FDRep.of ρ)) y :=
        ConcreteCategory.congr_hom hzero y
      _ = 0 := rfl
  · intro hne
    have hmap_ne : F.map f ≠ 0 := by
      intro h
      apply hne
      exact F.map_injective (by simpa using h)
    have hhom_ne : (F.map f).hom ≠ 0 := by
      intro h
      apply hmap_ne
      exact Rep.hom_ext h
    have hrep : (F.obj (FDRep.of ρ)).ρ = ρ := by
      simp only [F, FDRep.forget₂_ρ, FDRep.of_ρ']
      rfl
    let _ : (F.obj (FDRep.of ρ)).ρ.IsIrreducible :=
      hrep.symm ▸ (inferInstance : ρ.IsIrreducible)
    have hsurj : Function.Surjective (F.map f).hom :=
      (Representation.IsIrreducible.surjective_or_eq_zero (F.map f).hom).resolve_right hhom_ne
    have hmapEpi : Epi (F.map f) := (Rep.epi_iff_surjective (F.map f)).mpr hsurj
    let _ : Epi f := F.epi_of_epi_map hmapEpi
    exact isIso_of_mono_of_epi f

private def irrCharPairing {G : Type*} [Group G] [Finite G] (W : FDRep ℂ G) :
    (G → ℂ) →ₗ[ℂ] ℂ := by
  exact {
    toFun := fun f ↦ (Nat.card G : ℂ)⁻¹ * ∑ᶠ g, f g * W.character g⁻¹
    map_add' := by
      let _ := Fintype.ofFinite G
      intro f h
      simp only [finsum_eq_sum_of_fintype, Pi.add_apply, add_mul,
        Finset.sum_add_distrib, mul_add]
    map_smul' := by
      let _ := Fintype.ofFinite G
      intro c f
      simp only [finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      calc
        (Nat.card G : ℂ)⁻¹ * ∑ g, c * f g * W.character g⁻¹ =
            ∑ g, (Nat.card G : ℂ)⁻¹ * (c * f g * W.character g⁻¹) :=
          Finset.mul_sum _ _ _
        _ = ∑ g, c * ((Nat.card G : ℂ)⁻¹ * (f g * W.character g⁻¹)) := by
          apply Finset.sum_congr rfl
          intro g hg
          ring
        _ = c * ∑ g, (Nat.card G : ℂ)⁻¹ * (f g * W.character g⁻¹) :=
          (Finset.mul_sum _ _ _).symm
        _ = c * ((Nat.card G : ℂ)⁻¹ * ∑ g, f g * W.character g⁻¹) := by
          congr 1
          exact (Finset.mul_sum _ _ _).symm }

/-- Characters of pairwise nonisomorphic simple finite-dimensional complex
representations are linearly independent. -/
public theorem linearIndependent_character {I G : Type*} [Group G] [Finite G]
    (V : I → FDRep ℂ G) [∀ i, Simple (V i)]
    (hV : ∀ ⦃i j⦄, Nonempty (V i ≅ V j) → i = j) :
    LinearIndependent ℂ fun i ↦ (V i).character := by
  classical
  rw [linearIndependent_iff']
  intro s c h i hi
  have hp := congrArg (irrCharPairing (V i)) h
  simp only [map_zero, map_sum, map_smul] at hp
  have hpair : ∀ j, irrCharPairing (V i) (V j).character = if j = i then 1 else 0 := by
    intro j
    let _ := Fintype.ofFinite G
    change (Nat.card G : ℂ)⁻¹ * ∑ᶠ g, (V j).character g * (V i).character g⁻¹ = _
    rw [finsum_eq_sum_of_fintype, FDRep.char_orthonormal]
    by_cases hj : j = i
    · simp [hj]
    · have hno : ¬Nonempty (V j ≅ V i) := fun hIso ↦ hj (hV hIso)
      simp [hj, hno]
  simp_rw [hpair] at hp
  simpa [hi] using hp

private noncomputable def irrCharOp {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (f : G → ℂ) :
    Module.End ℂ V :=
  ∑ᶠ g, f g • ρ g⁻¹

private theorem irrCharOp_comm {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (f : G → ℂ) (hf : IsClassFunction f) (h : G) (x : V) :
    ρ h (irrCharOp ρ f x) = irrCharOp ρ f (ρ h x) := by
  classical
  let _ := Fintype.ofFinite G
  have hconj : ∀ u : G, f (u⁻¹ * h) = f (h * u⁻¹) := by
    intro u
    have h1 := hf (h * u⁻¹) u⁻¹
    rw [inv_inv] at h1
    have h2 : u⁻¹ * (h * u⁻¹) * u = u⁻¹ * h := by group
    rw [h2] at h1
    exact h1
  have eL_apply : ∀ u : G, (Equiv.inv G).trans (Equiv.mulRight h) u = u⁻¹ * h :=
    fun u ↦ rfl
  have eR_apply : ∀ u : G, (Equiv.inv G).trans (Equiv.mulLeft h) u = h * u⁻¹ :=
    fun u ↦ rfl
  have pushL : ρ h (∑ g, f g • ρ g⁻¹ x) = ∑ g, f g • ρ (h * g⁻¹) x := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [map_smul]
    congr 1
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, map_mul]
  have pushR : (∑ g, f g • ρ g⁻¹ (ρ h x)) = ∑ g, f g • ρ (g⁻¹ * h) x := by
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    congr 1
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, map_mul]
  have reL : (∑ g, f g • ρ (h * g⁻¹) x) = ∑ u, f (h * u⁻¹) • ρ u x := by
    rw [← Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulRight h))
      (fun g ↦ f g • ρ (h * g⁻¹) x)]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    show f ((Equiv.inv G).trans (Equiv.mulRight h) u) •
        ρ (h * ((Equiv.inv G).trans (Equiv.mulRight h) u)⁻¹) x = _
    rw [eL_apply]
    have harg : h * (u⁻¹ * h)⁻¹ = u := by group
    rw [harg, hconj u]
  have reR : (∑ g, f g • ρ (g⁻¹ * h) x) = ∑ u, f (h * u⁻¹) • ρ u x := by
    rw [← Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulLeft h))
      (fun g ↦ f g • ρ (g⁻¹ * h) x)]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    show f ((Equiv.inv G).trans (Equiv.mulLeft h) u) •
        ρ (((Equiv.inv G).trans (Equiv.mulLeft h) u)⁻¹ * h) x = _
    rw [eR_apply]
    have harg : (h * u⁻¹)⁻¹ * h = u := by group
    rw [harg]
  unfold irrCharOp
  simp only [finsum_eq_sum_of_fintype, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [pushL, pushR, reL, reR]

private noncomputable instance irrCharSmallMonoidAlgebra {G : Type*} [Finite G] :
    Small.{0} ℂ[G] :=
  (small_congr MonoidAlgebra.coeffEquiv).mpr inferInstance

private noncomputable def irrCharRegular {G : Type*} [Group G] [Finite G] :
    Representation ℂ G (Shrink.{0} ℂ[G]) :=
  (Shrink.linearEquiv ℂ ℂ[G]).symm.conjRingEquiv.toMonoidHom.comp
    (Representation.leftRegular ℂ G)

private theorem irrCharIrreducible_ofModule' {G : Type*} [Group G]
    (M : Type) [AddCommGroup M] [Module ℂ[G] M] [Module ℂ M]
    [IsScalarTower ℂ ℂ[G] M] [IsSimpleModule ℂ[G] M] :
    (Representation.ofModule' (k := ℂ) (G := G) M).IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have hAlg : (Representation.ofModule' (k := ℂ) (G := G) M).asAlgebraHom =
      Algebra.lsmul ℂ ℂ M := by
    simp only [Representation.asAlgebraHom_def, Representation.ofModule',
      Equiv.apply_symm_apply]
  have e : (Representation.ofModule' (k := ℂ) (G := G) M).asModule ≃ₗ[ℂ[G]] M :=
    { toFun := fun x ↦ (x : M)
      invFun := fun x ↦ (x : (Representation.ofModule' (k := ℂ) (G := G) M).asModule)
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        have h := Representation.asModuleEquiv_map_smul
          (ρ := Representation.ofModule' (k := ℂ) (G := G) M) r x
        rw [hAlg] at h
        simp only [Representation.asModuleEquiv, Algebra.lsmul_apply] at h
        exact h
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact IsSimpleModule.congr e

private theorem irrCharOp_smul_eq_zero {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (f : G → ℂ) (hf : IsClassFunction f) (a : ℂ[G]) :
    ∀ (x : ρ.asModule) (_ : irrCharOp ρ f (ρ.asModuleEquiv x) = 0),
      irrCharOp ρ f (ρ.asModuleEquiv (a • x)) = 0 := by
  refine MonoidAlgebra.induction_on
    (motive := fun a ↦ ∀ (x : ρ.asModule)
      (_ : irrCharOp ρ f (ρ.asModuleEquiv x) = 0),
      irrCharOp ρ f (ρ.asModuleEquiv (a • x)) = 0) a ?_ ?_ ?_
  · intro g x hx
    rw [MonoidAlgebra.of_apply]
    rw [Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_single_one,
      ← irrCharOp_comm ρ f hf g (ρ.asModuleEquiv x), hx, map_zero]
  · intro b c hb hc x hx
    rw [add_smul, map_add, map_add, hb x hx, hc x hx, add_zero]
  · intro c b hb x hx
    rw [smul_assoc, map_smul, map_smul, hb x hx, smul_zero]

private noncomputable def irrCharModuleOp {G M : Type*} [Group G] [Finite G]
    [AddCommGroup M] [Module ℂ[G] M] [Module ℂ M] [IsScalarTower ℂ ℂ[G] M]
    (f : G → ℂ) : Module.End ℂ M :=
  ∑ᶠ g, f g • (Representation.ofModule' (k := ℂ) (G := G) M) g⁻¹

private theorem irrCharModuleOp_comm {G M : Type*} [Group G] [Finite G]
    [AddCommGroup M] [Module ℂ[G] M] [Module ℂ M] [IsScalarTower ℂ ℂ[G] M]
    (f : G → ℂ) (hf : IsClassFunction f) (h : G) (x : M) :
    (Representation.ofModule' (k := ℂ) (G := G) M) h (irrCharModuleOp f x) =
      irrCharModuleOp f ((Representation.ofModule' (k := ℂ) (G := G) M) h x) := by
  classical
  let _ := Fintype.ofFinite G
  let σ := Representation.ofModule' (k := ℂ) (G := G) M
  have hconj : ∀ u : G, f (u⁻¹ * h) = f (h * u⁻¹) := by
    intro u
    have h1 := hf (h * u⁻¹) u⁻¹
    rw [inv_inv] at h1
    have h2 : u⁻¹ * (h * u⁻¹) * u = u⁻¹ * h := by group
    rw [h2] at h1
    exact h1
  have eL_apply : ∀ u : G, (Equiv.inv G).trans (Equiv.mulRight h) u = u⁻¹ * h :=
    fun u ↦ rfl
  have eR_apply : ∀ u : G, (Equiv.inv G).trans (Equiv.mulLeft h) u = h * u⁻¹ :=
    fun u ↦ rfl
  have pushL : σ h (∑ g, f g • σ g⁻¹ x) = ∑ g, f g • σ (h * g⁻¹) x := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [map_smul]
    congr 1
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, map_mul]
  have pushR : (∑ g, f g • σ g⁻¹ (σ h x)) = ∑ g, f g • σ (g⁻¹ * h) x := by
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    congr 1
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, map_mul]
  have reL : (∑ g, f g • σ (h * g⁻¹) x) = ∑ u, f (h * u⁻¹) • σ u x := by
    rw [← Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulRight h))
      (fun g ↦ f g • σ (h * g⁻¹) x)]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    show f ((Equiv.inv G).trans (Equiv.mulRight h) u) •
        σ (h * ((Equiv.inv G).trans (Equiv.mulRight h) u)⁻¹) x = _
    rw [eL_apply]
    have harg : h * (u⁻¹ * h)⁻¹ = u := by group
    rw [harg, hconj u]
  have reR : (∑ g, f g • σ (g⁻¹ * h) x) = ∑ u, f (h * u⁻¹) • σ u x := by
    rw [← Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulLeft h))
      (fun g ↦ f g • σ (g⁻¹ * h) x)]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    show f ((Equiv.inv G).trans (Equiv.mulLeft h) u) •
        σ (((Equiv.inv G).trans (Equiv.mulLeft h) u)⁻¹ * h) x = _
    rw [eR_apply]
    have harg : (h * u⁻¹)⁻¹ * h = u := by group
    rw [harg]
  unfold irrCharModuleOp
  simp only [finsum_eq_sum_of_fintype, LinearMap.sum_apply, LinearMap.smul_apply]
  change σ h (∑ g, f g • σ g⁻¹ x) = ∑ g, f g • σ g⁻¹ (σ h x)
  rw [pushL, pushR, reL, reR]

private theorem irrCharModuleOp_eq_smul {G : Type*} [Group G] [Finite G]
    (M : Type) [AddCommGroup M] [Module ℂ[G] M] [Module ℂ M]
    [IsScalarTower ℂ ℂ[G] M] [Module.Finite ℂ M] [IsSimpleModule ℂ[G] M]
    (f : G → ℂ) (hf : IsClassFunction f) :
    ∃ μ : ℂ, ∀ y : M, irrCharModuleOp f y = μ • y := by
  have hfin : FiniteDimensional ℂ M := inferInstance
  have hnt : Nontrivial M := IsSimpleModule.nontrivial ℂ[G] M
  have hirr : (Representation.ofModule' (k := ℂ) (G := G) M).IsIrreducible :=
    irrCharIrreducible_ofModule' M
  obtain ⟨μ, hμ⟩ := @Module.End.exists_eigenvalue ℂ M _ _ _ inferInstance hfin hnt
    (irrCharModuleOp f)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, fun y ↦ ?_⟩
  let E : Subrepresentation (Representation.ofModule' (k := ℂ) (G := G) M) :=
    { toSubmodule := Module.End.eigenspace (irrCharModuleOp f) μ
      apply_mem_toSubmodule := fun h y hy ↦ by
        rw [Module.End.mem_eigenspace_iff] at hy ⊢
        have hcomm := irrCharModuleOp_comm f hf h y
        rw [← hcomm, hy, map_smul] }
  have hET : E = ⊤ := by
    rcases @eq_bot_or_eq_top _ _ _ hirr E with hbot | htop
    · exfalso
      have hmem : v ∈ E.toSubmodule := hv.1
      rw [hbot] at hmem
      exact hv.2 hmem
    · exact htop
  have hmem : y ∈ E.toSubmodule := by
    rw [hET]
    exact Submodule.mem_top
  exact Module.End.mem_eigenspace_iff.mp hmem

private theorem irrCharModuleOp_eq_zero {G : Type*} [Group G] [Finite G]
    (M : Type) [AddCommGroup M] [Module ℂ[G] M] [Module ℂ M]
    [IsScalarTower ℂ ℂ[G] M] [Module.Finite ℂ M] [IsSimpleModule ℂ[G] M]
    (f : G → ℂ) (hf : IsClassFunction f)
    (horth : ∀ (W : FDRep ℂ G) [Simple W],
      (Nat.card G : ℂ)⁻¹ * ∑ᶠ g : G, f g * W.character g⁻¹ = 0) :
    irrCharModuleOp (M := M) f = 0 := by
  classical
  let _ := Fintype.ofFinite G
  have hirr : (Representation.ofModule' (k := ℂ) (G := G) M).IsIrreducible :=
    irrCharIrreducible_ofModule' M
  let _ := FDRep.simple_of_isIrreducible
    (Representation.ofModule' (k := ℂ) (G := G) M)
  obtain ⟨μ, hμ⟩ := irrCharModuleOp_eq_smul M f hf
  have horthM : (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g *
      (FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M)).character g⁻¹ = 0 := by
    simpa [finsum_eq_sum_of_fintype] using
      horth (FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M))
  have htrace : LinearMap.trace ℂ M (irrCharModuleOp f) = ∑ g : G, f g *
      (FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M)).character g⁻¹ := by
    unfold irrCharModuleOp
    rw [finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [map_smul]
    rfl
  have htrace_zero : LinearMap.trace ℂ M (irrCharModuleOp f) = 0 := by
    rw [htrace]
    have hne : (Nat.card G : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos)
    calc
      ∑ g : G, f g *
          (FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M)).character g⁻¹ =
          (Nat.card G : ℂ) * ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g *
            (FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M)).character g⁻¹) := by
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      _ = 0 := by rw [horthM, mul_zero]
  have hop : irrCharModuleOp (M := M) f = μ • (LinearMap.id : Module.End ℂ M) := by
    apply LinearMap.ext
    intro y
    simpa using hμ y
  have hμ_zero : μ = 0 := by
    have hfinrank : (Module.finrank ℂ M : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos_iff.mpr
        (IsSimpleModule.nontrivial ℂ[G] M)))
    rw [hop, map_smul, LinearMap.trace_id] at htrace_zero
    simp only [smul_eq_mul] at htrace_zero
    exact (mul_eq_zero.mp htrace_zero).resolve_right hfinrank
  rw [hop, hμ_zero, zero_smul]

private theorem irrCharRegular_op_eq_zero {G : Type*} [Group G] [Finite G]
    (f : G → ℂ) (hf : IsClassFunction f)
    (horth : ∀ (W : FDRep ℂ G) [Simple W],
      (Nat.card G : ℂ)⁻¹ * ∑ᶠ g : G, f g * W.character g⁻¹ = 0) :
    irrCharOp (irrCharRegular (G := G)) f = 0 := by
  classical
  let _ := Fintype.ofFinite G
  let _ : NeZero (Nat.card G : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos)⟩
  let ρ := irrCharRegular (G := G)
  let K : Submodule ℂ[G] ρ.asModule :=
    { carrier := {x | irrCharOp ρ f (ρ.asModuleEquiv x) = 0}
      add_mem' := by
        intro x y hx hy
        change irrCharOp ρ f (ρ.asModuleEquiv (x + y)) = 0
        rw [map_add, map_add, hx, hy, add_zero]
      zero_mem' := by
        change irrCharOp ρ f (ρ.asModuleEquiv 0) = 0
        rw [map_zero, map_zero]
      smul_mem' := by
        intro a x hx
        exact irrCharOp_smul_eq_zero ρ f hf a x hx }
  have hsimple_le (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S] : S ≤ K := by
    intro x hx
    let _ : FiniteDimensional ℂ S :=
      FiniteDimensional.of_injective (S.subtype.restrictScalars ℂ) S.injective_subtype
    have hvan : irrCharModuleOp (M := S) f = 0 :=
      irrCharModuleOp_eq_zero S f hf horth
    have hs0 : irrCharModuleOp (M := S) f (⟨x, hx⟩ : S) = 0 :=
      DFunLike.congr_fun hvan _
    change irrCharOp ρ f (ρ.asModuleEquiv x) = 0
    have hcompare :
        ρ.asModuleEquiv (S.subtype (irrCharModuleOp (M := S) f (⟨x, hx⟩ : S))) =
          irrCharOp ρ f (ρ.asModuleEquiv x) := by
      unfold irrCharModuleOp irrCharOp
      simp only [finsum_eq_sum_of_fintype, LinearMap.sum_apply, LinearMap.smul_apply]
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      rw [LinearMap.map_smul_of_tower, map_smul]
      congr 1
      change ρ.asModuleEquiv (S.subtype
        (MonoidAlgebra.single g⁻¹ (1 : ℂ) • (⟨x, hx⟩ : S))) = _
      rw [LinearMap.map_smul_of_tower,
        Representation.asModuleEquiv_map_smul,
        Representation.asAlgebraHom_single_one]
      rfl
    rw [← hcompare, hs0, map_zero, map_zero]
  have htop : K = ⊤ := by
    apply top_unique
    calc
      ⊤ = sSup {S : Submodule ℂ[G] ρ.asModule | IsSimpleModule ℂ[G] S} :=
        (IsSemisimpleModule.sSup_simples_eq_top ℂ[G] ρ.asModule).symm
      _ ≤ K := sSup_le fun S hS ↦ by
        let _ : IsSimpleModule ℂ[G] S := hS
        exact hsimple_le S
  apply LinearMap.ext
  intro y
  have hy : ρ.asModuleEquiv.symm y ∈ K := by
    rw [htop]
    exact Submodule.mem_top
  change irrCharOp ρ f (ρ.asModuleEquiv (ρ.asModuleEquiv.symm y)) = 0 at hy
  simpa [ρ] using hy

/-- A complex class function orthogonal to every irreducible character is zero. -/
public theorem eq_zero_of_isClassFunction_of_orthogonal {G : Type*} [Group G] [Finite G]
    (f : G → ℂ) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (horth : ∀ (W : FDRep ℂ G) [Simple W],
      (Nat.card G : ℂ)⁻¹ * ∑ᶠ g : G, f g * W.character g⁻¹ = 0) :
    f = 0 := by
  classical
  let _ := Fintype.ofFinite G
  let e := Shrink.linearEquiv ℂ ℂ[G]
  have hT := irrCharRegular_op_eq_zero f hf horth
  apply funext
  intro h
  have hT0 : irrCharOp (irrCharRegular (G := G)) f
      (e.symm (MonoidAlgebra.single h 1)) = 0 := DFunLike.congr_fun hT _
  have hA0 : e (irrCharOp (irrCharRegular (G := G)) f
      (e.symm (MonoidAlgebra.single h 1))) = 0 := by
    rw [hT0, map_zero]
  have hexpand : e (irrCharOp (irrCharRegular (G := G)) f
      (e.symm (MonoidAlgebra.single h 1))) =
      ∑ g : G, f g • MonoidAlgebra.single (g⁻¹ * h) (1 : ℂ) := by
    unfold irrCharOp
    simp only [finsum_eq_sum_of_fintype, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [map_smul]
    congr 1
    simp [e, irrCharRegular, Representation.ofMulAction_single]
  have hsum : (∑ g : G, f g • MonoidAlgebra.single (g⁻¹ * h) (1 : ℂ)) = 0 :=
    hexpand.symm.trans hA0
  have hcoeff := congrArg (fun a : ℂ[G] ↦ a.coeff 1) hsum
  have hsingle :
      (∑ g : G, f g • MonoidAlgebra.single (g⁻¹ * h) (1 : ℂ)).coeff 1 = f h := by
    simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      MonoidAlgebra.coeff_smul_apply]
    rw [Finset.sum_eq_single h]
    · simp
    · intro b hb hne
      have hprod : b⁻¹ * h ≠ 1 := by
        intro heq
        apply hne
        calc
          b = b * 1 := (mul_one b).symm
          _ = b * (b⁻¹ * h) := congrArg (b * ·) heq.symm
          _ = h := by group
      simp [hprod]
    · simp
  rw [hsingle] at hcoeff
  simpa using hcoeff

end FDRep

namespace MathlibExt.GroupTheory.IrreducibleCharacterBasisWanted

/-!
# Basis of irreducible characters

Row orthogonality of irreducible characters is `FDRep.char_orthonormal`; the
companion basis statements are recorded here: distinct irreducible complex
characters are linearly independent, they span the class functions, and there
are as many of them as conjugacy classes.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "orthonormal basis of irreducible characters" (reference-only, no Lean
formalization); J.-P. Serre, Linear Representations of Finite Groups, GTM 42,
§2.5–§2.7 (orthogonality relations and the basis theorem).
-/

/--
Distinct irreducible complex characters are linearly independent as functions.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "orthonormal basis of irreducible characters"; J.-P. Serre, Linear
Representations of Finite Groups, GTM 42, §2.5 (independence of irreducible
characters).

Proves `Wanted` entry `linearIndependent_irrCharacters`.

Proof: Apply row orthogonality (C. Teleman, *Representation Theory*, Cambridge lecture
notes, 2005, Theorem 8.10) as coordinate functionals to a vanishing finite linear
combination of pairwise distinct irreducible characters.
-/
public theorem linearIndependent_irrCharacters (G : Type*) [Group G]
    [Finite G] :
    LinearIndependent ℂ (Subtype.val :
      {χ : G → ℂ // ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ} → (G → ℂ)) := by
  classical
  let V : {χ : G → ℂ // ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ} → FDRep ℂ G :=
    fun χ ↦ Classical.choose χ.property
  let _ : ∀ χ, Simple (V χ) := fun χ ↦ (Classical.choose_spec χ.property).1
  have hchar (χ) : (V χ).character = χ.1 := (Classical.choose_spec χ.property).2
  have hnoniso : ∀ ⦃χ ψ⦄, Nonempty (V χ ≅ V ψ) → χ = ψ := by
    intro χ ψ h
    apply Subtype.ext
    rw [← hchar χ, ← hchar ψ]
    exact FDRep.char_iso h.some
  have hLI := FDRep.linearIndependent_character V hnoniso
  convert hLI using 1
  ext χ g
  exact (congrFun (hchar χ) g).symm

/--
Every class function is a linear combination of irreducible characters.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "orthonormal basis of irreducible characters"; J.-P. Serre, Linear
Representations of Finite Groups, GTM 42, §2.7, Theorem 6 (irreducible
characters span the class functions).

Proves `Wanted` entry `mem_span_irrCharacters_of_isClassFunction`.

Proof: Subtract the orthogonal projection onto the irreducible characters. The
remainder vanishes by Schur's lemma, Maschke's theorem, and the regular
representation on a small model of the complex group algebra, as in the proof of
Teleman's Theorem 9.3 (completeness of characters).
-/
public theorem mem_span_irrCharacters_of_isClassFunction (G : Type*)
    [Group G] [Finite G] (f : G → ℂ) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    f ∈ Submodule.span ℂ
      {χ : G → ℂ | ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ} := by
  classical
  let _ := Fintype.ofFinite G
  let I := {χ : G → ℂ // ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ}
  let _ : Finite I := (linearIndependent_irrCharacters G).finite
  let _ := Fintype.ofFinite I
  let coeff : I → ℂ := fun χ ↦
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * χ.1 g⁻¹
  let p : G → ℂ := ∑ χ : I, coeff χ • χ.1
  have hchar_class (χ : I) : ∀ g h : G, χ.1 (h * g * h⁻¹) = χ.1 g := by
    obtain ⟨V, hV, hχ⟩ := χ.property
    rw [← hχ]
    exact character_isClassFunction V
  have hp_class : ∀ g h : G, p (h * g * h⁻¹) = p g := by
    intro g h
    simp only [p, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun χ _ ↦ ?_
    rw [hchar_class χ g h]
  have hd_class : ∀ g h : G, (f - p) (h * g * h⁻¹) = (f - p) g := by
    intro g h
    simp only [Pi.sub_apply]
    rw [hf g h, hp_class g h]
  have horth : ∀ (W : FDRep ℂ G) [Simple W],
      (Nat.card G : ℂ)⁻¹ * ∑ᶠ g : G, (f - p) g * W.character g⁻¹ = 0 := by
    intro W hW
    let χW : I := ⟨W.character, W, hW, rfl⟩
    have hpair (χ : I) : FDRep.irrCharPairing W χ.1 = if χ = χW then 1 else 0 := by
      by_cases heq : χ = χW
      · subst χ
        rw [ite_eq_left rfl]
        unfold FDRep.irrCharPairing
        change (Nat.card G : ℂ)⁻¹ *
          ∑ᶠ g : G, W.character g * W.character g⁻¹ = 1
        rw [finsum_eq_sum_of_fintype]
        have hself := FDRep.char_orthonormal W W
        rw [ite_eq_left ⟨Iso.refl W⟩] at hself
        exact hself
      · obtain ⟨V, hV, hχ⟩ := χ.property
        rw [ite_eq_right heq]
        unfold FDRep.irrCharPairing
        change (Nat.card G : ℂ)⁻¹ *
          ∑ᶠ g : G, χ.1 g * W.character g⁻¹ = 0
        rw [finsum_eq_sum_of_fintype]
        rw [← hχ, FDRep.char_orthonormal]
        have hno : ¬Nonempty (V ≅ W) := by
          intro hIso
          apply heq
          apply Subtype.ext
          exact hχ.symm.trans (FDRep.char_iso hIso.some)
        simp [hno]
    have hp_pair : FDRep.irrCharPairing W p = coeff χW := by
      simp only [p, map_sum, map_smul, hpair]
      simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
      exact Fintype.sum_ite_eq' χW coeff
    change FDRep.irrCharPairing W (f - p) = 0
    rw [map_sub, hp_pair]
    have hf_pair : FDRep.irrCharPairing W f = coeff χW := by
      unfold FDRep.irrCharPairing
      change (Nat.card G : ℂ)⁻¹ * ∑ᶠ g : G, f g * W.character g⁻¹ = coeff χW
      rw [finsum_eq_sum_of_fintype]
    rw [hf_pair, sub_self]
  have hzero := FDRep.eq_zero_of_isClassFunction_of_orthogonal (f - p) hd_class horth
  have hfp : f = p := sub_eq_zero.mp hzero
  rw [hfp]
  apply Submodule.sum_mem
  intro χ hχ
  exact Submodule.smul_mem _ _ (Submodule.subset_span χ.property)

/--
The number of irreducible complex characters equals the number of conjugacy
classes.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "orthonormal basis of irreducible characters"; J.-P. Serre, Linear
Representations of Finite Groups, GTM 42, §2.7 (number of irreducible
characters).

Proves `Wanted` entry `card_irrCharacters_eq_card_conjClasses`.

Proof: The first two theorems identify the irreducible characters as a basis of
the class functions; compare its cardinality with the known finrank of that
space (P. Etingof et al., *Introduction to representation theory*, arXiv:0901.0827,
Theorem 3.5 and Corollary 3.6).
-/
public theorem card_irrCharacters_eq_card_conjClasses (G : Type*)
    [Group G] [Finite G] :
    Nat.card {χ : G → ℂ // ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ} =
      Nat.card (ConjClasses G) := by
  classical
  let _ := Fintype.ofFinite G
  let I := {χ : G → ℂ // ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ}
  let _ : Finite I := (linearIndependent_irrCharacters G).finite
  let _ := Fintype.ofFinite I
  have hspan : Submodule.span ℂ
      {χ : G → ℂ | ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ} =
      classFunctions G ℂ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro χ hχ
      obtain ⟨V, hV, hchar⟩ := hχ
      change IsClassFunction χ
      rw [← hchar]
      exact character_isClassFunction V
    · intro f hf
      exact mem_span_irrCharacters_of_isClassFunction G f hf
  have hfinrank := finrank_span_eq_card (linearIndependent_irrCharacters G)
  change Module.finrank ℂ ↥(Submodule.span ℂ
    (Set.range (Subtype.val : I → (G → ℂ)))) = Fintype.card I at hfinrank
  have hrange : Set.range (Subtype.val : I → (G → ℂ)) =
      {χ : G → ℂ | ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ} :=
    Subtype.range_val
  rw [hrange, hspan] at hfinrank
  change Nat.card I = Nat.card (ConjClasses G)
  rw [Nat.card_eq_fintype_card]
  exact hfinrank.symm.trans (finrank_classFunctions_eq_card_conjClasses G ℂ)

end MathlibExt.GroupTheory.IrreducibleCharacterBasisWanted
