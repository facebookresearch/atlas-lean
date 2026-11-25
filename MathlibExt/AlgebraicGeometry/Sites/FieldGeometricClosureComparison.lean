/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import MathlibExt.Algebra.Category.CommAlgCat.FiniteEtale.SeparableClosure
public import MathlibExt.AlgebraicGeometry.Sites.FieldFiniteEtaleBasis
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGeometricPointsCommonUniverse
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Sites.Point.Category

/-!
# Comparison of all original geometric point fibers under a compatible closure embedding
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

variable (k Ω Ψ : Type u) [Field k] [Field Ω] [Field Ψ]
variable [Algebra k Ω] [Algebra k Ψ]

/-- The scheme morphism from Spec Ψ to Spec Ω induced by the algebra homomorphism σ. -/
def fieldClosureSpec (σ : Ω →ₐ[k] Ψ) : Spec (.of Ψ) ⟶ Spec (.of Ω) :=
  Spec.map (CommRingCat.ofHom σ.toRingHom)

/-- The original field embedding is flat and surjective on its actual spectra. -/
theorem fieldClosureSpec_epi (σ : Ω →ₐ[k] Ψ) : Epi (fieldClosureSpec k Ω Ψ σ) := by
  let : Algebra Ω Ψ := σ.toRingHom.toAlgebra
  have hff : σ.toRingHom.FaithfullyFlat := by
    change Module.FaithfullyFlat Ω Ψ
    infer_instance
  have h := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom σ.toRingHom)).mpr hff
  let : Flat (fieldClosureSpec k Ω Ψ σ) := h.1
  let : Surjective (fieldClosureSpec k Ω Ψ σ) := h.2
  exact Flat.epi_of_flat_of_surjective _

/-- The morphism over Spec k from the Ψ-valued point to the Ω-valued point induced by σ. -/
def fieldClosureOverHom (σ : Ω →ₐ[k] Ψ) :
    Over.mk (Spec.algebraMap k Ψ) ⟶ Over.mk (Spec.algebraMap k Ω) :=
  Over.homMk (fieldClosureSpec k Ω Ψ σ) (by
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.algebraMap k Ω =
      Spec.algebraMap k Ψ
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact σ.commutes a)

variable [IsSepClosure k Ω] [IsSepClosed Ψ]
attribute [local instance] IsSepClosure.sep_closed

/-- This is the original point morphism, with the contravariant Point.Hom orientation. -/
def fieldClosurePointHom (σ : Ω →ₐ[k] Ψ) :
    Scheme.pointSmallEtale (Spec.algebraMap k Ψ) ⟶
      Scheme.pointSmallEtale (Spec.algebraMap k Ω) where
  hom := Functor.whiskerLeft (Scheme.Etale.forget (Spec (.of k)))
    (coyoneda.map (fieldClosureOverHom k Ω Ψ σ).op)

theorem fieldClosurePointHom_app_left (σ : Ω →ₐ[k] Ψ)
    (U : (Spec (.of k)).Etale)
    (z : (Scheme.pointSmallEtale (Spec.algebraMap k Ω)).fiber.obj U) :
    (((fieldClosurePointHom k Ω Ψ σ).hom.app U) z).left =
      fieldClosureSpec k Ω Ψ σ ≫ z.left := rfl

theorem fieldClosurePointHom_app_injective (σ : Ω →ₐ[k] Ψ)
    (U : (Spec (.of k)).Etale) :
    Function.Injective ((fieldClosurePointHom k Ω Ψ σ).hom.app U) := by
  let : Epi (fieldClosureSpec k Ω Ψ σ) := fieldClosureSpec_epi k Ω Ψ σ
  intro x y h
  apply Over.OverMorphism.ext
  apply (cancel_epi (fieldClosureSpec k Ω Ψ σ)).mp
  exact congrArg (fun z => z.left) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The retained v1 proof reached an implicit-transparency @Etale/Over type mismatch.
/-- Every original point of every possibly nonaffine/infinite-component object lifts. -/
theorem fieldClosurePointHom_app_surjective (σ : Ω →ₐ[k] Ψ)
    (U : (Spec (.of k)).Etale) :
    Function.Surjective ((fieldClosurePointHom k Ω Ψ σ).hom.app U) := by
  intro z
  let : Etale U.hom := U.prop
  let z0 : Spec (.of Ψ) ⟶ U.left := z.left
  have hz0 : z0 ≫ U.hom = Spec.algebraMap k Ψ := Over.w z
  obtain ⟨R, j, _, hj, _⟩ := exists_affine_mem_range_and_range_subset
    (x := z0.base default) (U := ⊤) (by simp)
  have hrange : Set.range z0.base ⊆ Set.range j.base := by
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  let y := IsOpenImmersion.lift j z0 hrange
  have hy : y ≫ j = z0 := IsOpenImmersion.lift_fac j z0 hrange
  let f := j ≫ U.hom
  let : Algebra k R := (Spec.preimage f).hom.toAlgebra
  have hf : Spec.algebraMap k R = f := Spec.map_preimage f
  have hr : (algebraMap k R).Etale := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [Spec.map_preimage]
    dsimp [f]
    infer_instance
  let : Algebra.Etale k R := (RingHom.etale_algebraMap).mp hr
  let : Module.Free k R := Module.Free.of_divisionRing k R
  let : Module.Finite k R := Algebra.FormallyUnramified.finite_of_free k R
  have hyf : y ≫ Spec.algebraMap k R = Spec.algebraMap k Ψ := by
    exact (congrArg (y ≫ ·) hf).trans
      ((Category.assoc y j U.hom).symm.trans
        ((congrArg (· ≫ U.hom) hy).trans hz0))
  let μ : R →ₐ[k] Ψ := Spec.homEquivAlgHom ⟨y, hyf⟩
  let A : CommAlgCat.FiniteEtale.{u} k := CommAlgCat.FiniteEtale.of k R
  let μΩ : R →ₐ[k] Ω :=
    CommAlgCat.FiniteEtale.liftAlgHom k Ω Ψ σ A μ
  let r0 := Spec.map (CommRingCat.ofHom μΩ.toRingHom)
  have hcomp : fieldClosureSpec k Ω Ψ σ ≫ r0 = y := by
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom μΩ.toRingHom) = y
    rw [← Spec.map_comp]
    have hm := CommAlgCat.FiniteEtale.liftAlgHom_spec k Ω Ψ σ A μ
    calc
      _ = Spec.map (CommRingCat.ofHom μ.toRingHom) := by
        congr 1
        ext a
        exact congrArg (fun g : R →ₐ[k] Ψ => g a) hm
      _ = y := Spec.map_preimage y
  have hr0 : (r0 ≫ j) ≫ U.hom = Spec.algebraMap k Ω := by
    exact (Category.assoc r0 j U.hom).trans
      ((congrArg (r0 ≫ ·) hf.symm).trans
        ((Spec.homEquivAlgHom (R := k) (A := R) (B := Ω)).symm μΩ).property)
  refine ⟨Over.homMk (r0 ≫ j) hr0, ?_⟩
  apply Over.OverMorphism.ext
  change fieldClosureSpec k Ω Ψ σ ≫ (r0 ≫ j) = z0
  rw [← Category.assoc, hcomp, hy]

/-- The literal original point-component map is an isomorphism on the full site. -/
def fieldClosureFiberIso (σ : Ω →ₐ[k] Ψ) :
    (Scheme.pointSmallEtale (Spec.algebraMap k Ω)).fiber ≅
      (Scheme.pointSmallEtale (Spec.algebraMap k Ψ)).fiber :=
  NatIso.ofComponents (fun U => (Equiv.ofBijective
    ((fieldClosurePointHom k Ω Ψ σ).hom.app U)
    ⟨fieldClosurePointHom_app_injective k Ω Ψ σ U,
      fieldClosurePointHom_app_surjective k Ω Ψ σ U⟩).toIso)
    (fun f => (fieldClosurePointHom k Ω Ψ σ).hom.naturality f)

/-- The small étale point isomorphism induced by the relative separable closure embedding σ. -/
def fieldClosurePointIso (σ : Ω →ₐ[k] Ψ) :
    Scheme.pointSmallEtale (Spec.algebraMap k Ψ) ≅
      Scheme.pointSmallEtale (Spec.algebraMap k Ω) where
  hom := fieldClosurePointHom k Ω Ψ σ
  inv := ⟨(fieldClosureFiberIso k Ω Ψ σ).inv⟩
  hom_inv_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (fieldClosureFiberIso k Ω Ψ σ).inv_hom_id
  inv_hom_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (fieldClosureFiberIso k Ω Ψ σ).hom_inv_id

/-- The same comparison lifts original point elements once to the common size. -/
def fieldClosureCommonPointIso (σ : Ω →ₐ[k] Ψ) :
    smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ψ) ≅
      smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω) where
  hom := ⟨Functor.whiskerRight (fieldClosurePointHom k Ω Ψ σ).hom uliftFunctor.{w, u}⟩
  inv := ⟨(Functor.isoWhiskerRight (fieldClosureFiberIso k Ω Ψ σ) uliftFunctor.{w, u}).inv⟩
  hom_inv_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (Functor.isoWhiskerRight (fieldClosureFiberIso k Ω Ψ σ) uliftFunctor.{w, u}).inv_hom_id
  inv_hom_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (Functor.isoWhiskerRight (fieldClosureFiberIso k Ω Ψ σ) uliftFunctor.{w, u}).hom_inv_id

/-- One natural additive comparison on the SAME actual original/common stalks. -/
def fieldClosureCommonStalkIso (σ : Ω →ₐ[k] Ψ) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
        (A := AddCommGrpCat.{max u w}) ≅
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ψ)).sheafFiber
        (A := AddCommGrpCat.{max u w}) where
  hom := (fieldClosureCommonPointIso.{u, w} k Ω Ψ σ).hom.sheafFiber
  inv := (fieldClosureCommonPointIso.{u, w} k Ω Ψ σ).inv.sheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
      (fieldClosureCommonPointIso.{u, w} k Ω Ψ σ).inv_hom_id]
    exact GrothendieckTopology.Point.Hom.sheafFiber_id _
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
      (fieldClosureCommonPointIso.{u, w} k Ω Ψ σ).hom_inv_id]
    exact GrothendieckTopology.Point.Hom.sheafFiber_id _

theorem fieldClosureCommonStalkIso_original_germ (σ : Ω →ₐ[k] Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (U : (Spec (.of k)).Etale)
    (z : (Scheme.pointSmallEtale (Spec.algebraMap k Ω)).fiber.obj U) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber U
        (ULift.up z) Q.obj ≫ (fieldClosureCommonStalkIso.{u, w} k Ω Ψ σ).hom.app Q =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ψ)).toPresheafFiber U
        (ULift.up (((fieldClosurePointHom k Ω Ψ σ).hom.app U) z)) Q.obj := by
  change _ ≫ (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).presheafFiberDesc
    (A := AddCommGrpCat.{max u w}) (P := Q.obj) _ _ = _
  exact (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber_presheafFiberDesc
    (A := AddCommGrpCat.{max u w}) (P := Q.obj) _ _ U (ULift.up z)

end AlgebraicGeometry.Scheme.DerivedSections

end
