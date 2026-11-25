/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.LinearAlgebra.Dimension.Free

/-! # Finite Galois refinements of the original field geometric neighborhoods

The field, chosen separable closure, original étale objects and geometric
maps are retained. Finite Galois fields lie inside that same closure.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The prescribed original geometric point of the field site. -/
def fieldGeometricPoint : (Spec (.of k)).smallEtaleTopology.Point :=
  Scheme.pointSmallEtale (Spec.algebraMap k Ω)

/-- Its actual original geometric-neighborhood category. -/
abbrev FieldGeometricNeighborhoods := (fieldGeometricPoint k Ω).fiber.Elements

theorem fieldFiniteGalois_algHom_factor {A : Type u} [CommRing A] [Algebra k A]
    [Module.Finite k A] (f : A →ₐ[k] Ω) :
    ∃ (L : FiniteGaloisIntermediateField k Ω) (fL : A →ₐ[k] L),
      (IsScalarTower.toAlgHom k L Ω).comp fL = f := by
  classical
  let b := Module.finBasis k A
  let S : Set Ω := Set.range (fun i => f (b i))
  let L := FiniteGaloisIntermediateField.adjoin k S
  have hb (i) : f (b i) ∈ L.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin k S ⟨i, rfl⟩
  have hspan : Submodule.span k (Set.range b) ≤
      (L.toIntermediateField.toSubalgebra.toSubmodule).comap f.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hb i
  have hf (a : A) : f a ∈ L.toIntermediateField := by
    change a ∈ (L.toIntermediateField.toSubalgebra.toSubmodule).comap f.toLinearMap
    apply hspan
    rw [b.span_eq]
    trivial
  let fL : A →ₐ[k] L := f.codRestrict L.toIntermediateField.toSubalgebra hf
  refine ⟨L, fL, ?_⟩
  ext a
  rfl

/-- A finite Galois subfield gives its actual original étale object. -/
abbrev fieldFiniteGaloisEtale (L : FiniteGaloisIntermediateField k Ω) :
    (Spec (.of k)).Etale := by
  letI : Algebra.FormallyEtale k L := Algebra.FormallyEtale.of_isSeparable k L
  letI : Algebra.FinitePresentation k L :=
    (Algebra.FinitePresentation.of_finiteType (R := k) (A := L)).mp inferInstance
  letI : Algebra.Etale k L := { }
  have h : Etale (Spec.algebraMap k L) := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    exact (RingHom.etale_algebraMap).mpr inferInstance
  exact Scheme.Etale.mk (Spec.algebraMap k L)

/-- Its original geometric lift is the spectrum of the same subfield inclusion. -/
def fieldFiniteGaloisPoint (L : FiniteGaloisIntermediateField k Ω) :
    (fieldGeometricPoint k Ω).fiber.obj (fieldFiniteGaloisEtale k Ω L) :=
  Over.homMk (Spec.algebraMap L Ω)
    ((Spec.homEquivAlgHom (R := k) (A := L) (B := Ω)).symm
      (IsScalarTower.toAlgHom k L Ω)).property

/-- The actual pointed original étale object. -/
def fieldFiniteGaloisNeighborhood (L : FiniteGaloisIntermediateField k Ω) :
    FieldGeometricNeighborhoods k Ω :=
  Functor.elementsMk _ (fieldFiniteGaloisEtale k Ω L) (fieldFiniteGaloisPoint k Ω L)

/-- Every subfield inclusion gives the original spectrum arrow in the reverse direction. -/
def fieldFiniteGaloisInclusion {L M : FiniteGaloisIntermediateField k Ω} (h : L ≤ M) :
    fieldFiniteGaloisEtale k Ω M ⟶ fieldFiniteGaloisEtale k Ω L :=
  MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom))
    ((Spec.homEquivAlgHom (R := k) (A := L) (B := M)).symm
      (IntermediateField.inclusion h)).property

theorem fieldFiniteGaloisInclusion_point
    {L M : FiniteGaloisIntermediateField k Ω} (h : L ≤ M) :
    (fieldGeometricPoint k Ω).fiber.map (fieldFiniteGaloisInclusion k Ω h)
        (fieldFiniteGaloisPoint k Ω M) = fieldFiniteGaloisPoint k Ω L := by
  apply Over.OverMorphism.ext
  change Spec.algebraMap M Ω ≫
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) =
    Spec.algebraMap L Ω
  rw [← Spec.map_comp]
  congr 1

/-- The canonical finite Galois subfield functor into opposite original neighborhoods. -/
def fieldFiniteGaloisNeighborhoodFunctor :
    FiniteGaloisIntermediateField k Ω ⥤ (FieldGeometricNeighborhoods k Ω)ᵒᵖ where
  obj L := op (fieldFiniteGaloisNeighborhood k Ω L)
  map f := (Functor.Elements.homMk (fieldFiniteGaloisInclusion k Ω (leOfHom f))
    (fieldFiniteGaloisInclusion_point k Ω (leOfHom f))).op
  map_id L := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom
      (IntermediateField.inclusion (E := L.toIntermediateField)
        (F := L.toIntermediateField) le_rfl).toRingHom) = 𝟙 (Spec (.of L))
    rw [IntermediateField.inclusion_self]
    have e : CommRingCat.ofHom (AlgHom.id k L).toRingHom = 𝟙 (CommRingCat.of L) := by
      ext x; rfl
    exact (congrArg Spec.map e).trans (Spec.map_id _)
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom (f ≫ g))).toRingHom) =
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom g)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom)
    rw [← Spec.map_comp]
    congr 1

/-- Every original geometric map, with no affine assumption on its original target, refines. -/
theorem fieldFiniteGalois_refines
    (U : (Spec (.of k)).Etale) (z : Spec (.of Ω) ⟶ U.left)
    (hz : z ≫ U.hom = Spec.algebraMap k Ω) :
    ∃ (L : FiniteGaloisIntermediateField k Ω) (r : Spec (.of L) ⟶ U.left),
      r ≫ U.hom = Spec.algebraMap k L ∧ Spec.algebraMap L Ω ≫ r = z := by
  obtain ⟨R, j, _, hj, _⟩ := exists_affine_mem_range_and_range_subset
    (x := z.base default) (U := ⊤) (by simp)
  have hrange : Set.range z.base ⊆ Set.range j.base := by
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  let y := IsOpenImmersion.lift j z hrange
  have hy : y ≫ j = z := IsOpenImmersion.lift_fac j z hrange
  let f := j ≫ U.hom
  let : Algebra k R := (Spec.preimage f).hom.toAlgebra
  have hf : Spec.algebraMap k R = f := Spec.map_preimage f
  have hr : (algebraMap k R).Etale := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [Spec.map_preimage]
    infer_instance
  let : Algebra.Etale k R := (RingHom.etale_algebraMap).mp hr
  let : Module.Finite k R := Algebra.FormallyUnramified.finite_of_free k R
  have hyf : y ≫ Spec.algebraMap k R = Spec.algebraMap k Ω := by
    rw [hf]
    change y ≫ (j ≫ U.hom) = _
    rw [← Category.assoc, hy, hz]
  let μ : R →ₐ[k] Ω := Spec.homEquivAlgHom ⟨y, hyf⟩
  have hμ : Spec.map (CommRingCat.ofHom μ.toRingHom) = y := by
    change Spec.map (Spec.preimage y) = y
    exact Spec.map_preimage y
  obtain ⟨L, μL, hcomp⟩ := fieldFiniteGalois_algHom_factor k Ω μ
  let r0 := Spec.map (CommRingCat.ofHom μL.toRingHom)
  have hry : Spec.algebraMap L Ω ≫ r0 = y := by
    calc
      _ = Spec.map ((CommRingCat.ofHom μL.toRingHom) ≫
          (CommRingCat.ofHom (algebraMap L Ω))) := (Spec.map_comp _ _).symm
      _ = Spec.map (CommRingCat.ofHom μ.toRingHom) := by
        congr 1
        ext a
        exact congrArg (fun t : R →ₐ[k] Ω => t a) hcomp
      _ = y := hμ
  refine ⟨L, r0 ≫ j, ?_, ?_⟩
  · calc
      (r0 ≫ j) ≫ U.hom = r0 ≫ (j ≫ U.hom) := Category.assoc _ _ _
      _ = r0 ≫ Spec.algebraMap k R := congrArg (fun t => r0 ≫ t) hf.symm
      _ = Spec.algebraMap k L :=
        ((Spec.homEquivAlgHom (R := k) (A := R) (B := L)).symm μL).property
  · rw [← Category.assoc, hry, hy]

/-- The same refinement in the literal original point-fiber category. -/
theorem fieldFiniteGalois_refines_point
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    ∃ (L : FiniteGaloisIntermediateField k Ω)
      (r : fieldFiniteGaloisEtale k Ω L ⟶ U),
      (fieldGeometricPoint k Ω).fiber.map r (fieldFiniteGaloisPoint k Ω L) = z := by
  obtain ⟨L, r, hr, hz⟩ := fieldFiniteGalois_refines k Ω U z.left (Over.w z)
  let r' : fieldFiniteGaloisEtale k Ω L ⟶ U := MorphismProperty.Over.homMk r hr
  refine ⟨L, r', ?_⟩
  apply Over.OverMorphism.ext
  exact hz

/-- Every opposite original neighborhood has an actual arrow to the same finite subfield functor. -/
theorem fieldFiniteGaloisNeighborhoodFunctor_refines
    (d : (FieldGeometricNeighborhoods k Ω)ᵒᵖ) :
    ∃ L, Nonempty (d ⟶ (fieldFiniteGaloisNeighborhoodFunctor k Ω).obj L) := by
  obtain ⟨L, r, hr⟩ := fieldFiniteGalois_refines_point k Ω d.unop.obj d.unop.val
  exact ⟨L, ⟨(Functor.Elements.homMk r hr).op⟩⟩

/-- The full original finite Galois pointed-refinement unit and its literal functor laws. -/
theorem original_field_finite_galois_pointed_neighborhoods :
    (∀ L, (fieldFiniteGaloisNeighborhoodFunctor k Ω).obj L =
      op (fieldFiniteGaloisNeighborhood k Ω L)) ∧
    (∀ {L M} (f : L ⟶ M),
      ((fieldFiniteGaloisNeighborhoodFunctor k Ω).map f).unop.hom.left =
        Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom)) ∧
    (∀ L, (fieldFiniteGaloisNeighborhoodFunctor k Ω).map (𝟙 L) =
      𝟙 ((fieldFiniteGaloisNeighborhoodFunctor k Ω).obj L)) ∧
    (∀ {L M N} (f : L ⟶ M) (g : M ⟶ N),
      (fieldFiniteGaloisNeighborhoodFunctor k Ω).map (f ≫ g) =
        (fieldFiniteGaloisNeighborhoodFunctor k Ω).map f ≫
          (fieldFiniteGaloisNeighborhoodFunctor k Ω).map g) ∧
    (∀ (U : (Spec (.of k)).Etale) (z : Spec (.of Ω) ⟶ U.left)
      (_hz : z ≫ U.hom = Spec.algebraMap k Ω),
      ∃ (L : FiniteGaloisIntermediateField k Ω) (r : Spec (.of L) ⟶ U.left),
        r ≫ U.hom = Spec.algebraMap k L ∧ Spec.algebraMap L Ω ≫ r = z) ∧
    ∀ d : (FieldGeometricNeighborhoods k Ω)ᵒᵖ,
      ∃ L, Nonempty (d ⟶ (fieldFiniteGaloisNeighborhoodFunctor k Ω).obj L) := by
  exact ⟨fun _ => rfl, fun _ => rfl,
    (fieldFiniteGaloisNeighborhoodFunctor k Ω).map_id,
    (fieldFiniteGaloisNeighborhoodFunctor k Ω).map_comp,
    fieldFiniteGalois_refines k Ω, fieldFiniteGaloisNeighborhoodFunctor_refines k Ω⟩

end AlgebraicGeometry.Scheme.DerivedSections
