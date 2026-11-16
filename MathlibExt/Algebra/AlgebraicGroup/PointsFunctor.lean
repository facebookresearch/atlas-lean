/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Source port of TauCeti/Algebra/AlgebraicGroup/PointsFunctor.lean.
TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Modifications: change only project namespaces and import paths.
The original Apache 2.0 copyright and authors above are retained.
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import MathlibExt.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# The functor of points of a Hopf algebra

This file packages the convolution group of algebra homomorphisms out of a Hopf algebra as a
functor from commutative algebras to groups. For a Hopf algebra `H` over `R`, an object
`A : CommAlgCat R` is sent to the convolution group on `H →ₐ[R] A`; a morphism
`φ : A ⟶ B` acts by post-composition with `φ`.

When `H` is commutative, this is the functor of points of the affine group scheme that `H`
represents: its values are `A ↦ (H →ₐ[R] A)`, with the convolution group law.

## Main definitions

* `MathlibExt.HopfAlgebra.points`: the bundled group of `A`-points.
* `MathlibExt.HopfAlgebra.extendPoint`: extension of ground-ring-valued points to a value algebra.
* `MathlibExt.HopfAlgebra.mapPoints`: the group homomorphism induced by post-composition in the
  value
  algebra.
* `MathlibExt.HopfAlgebra.pointsFunctor`: the functor `CommAlgCat R ⥤ GrpCat`.
* `MathlibExt.HopfAlgebra.subgroupFunctor`: the functor of a family of point subgroups stable under
  change of value algebra, with its natural inclusion `MathlibExt.HopfAlgebra.subgroupFunctorIncl`.

## References

The construction builds on Mathlib's convolution monoid for algebra homomorphisms and on the
convolution-group inverse of `MathlibExt.Algebra.AlgebraicGroup.FunctorOfPoints`.
-/

public section

open CategoryTheory WithConv

namespace MathlibExt

namespace HopfAlgebra

universe u v w x

variable {R : Type u} [CommRing R] {H : Type v} [Semiring H] [_root_.HopfAlgebra R H]

/-- The group of `A`-points of a Hopf algebra `H`; when `H` is commutative, these are the
`A`-points of the affine group scheme it represents.

The underlying type is `WithConv (H →ₐ[R] A)`: algebra homomorphisms from `H` to `A`, with
the convolution group structure supplied by the antipode of `H`. -/
noncomputable abbrev points (A : CommAlgCat.{w} R) : GrpCat.{max v w} :=
  GrpCat.of (WithConv (H →ₐ[R] A))

/-- Extension of ground-ring-valued points to `A`-valued points along the structure map of `A`. -/
noncomputable def extendPoint (H : Type v) [Semiring H] [_root_.HopfAlgebra R H]
    (A : CommAlgCat.{w} R) :
    points (H := H) (CommAlgCat.of R R) →* points (H := H) A :=
  AlgHom.mapValue (Algebra.ofId R A)

/-- Extension of a point is post-composition with the value algebra's structure map. -/
theorem extendPoint_apply (H : Type v) [Semiring H] [_root_.HopfAlgebra R H]
    (A : CommAlgCat.{w} R) (g : points (H := H) (CommAlgCat.of R R)) :
    extendPoint H A g = toConv ((Algebra.ofId R A).comp g.ofConv) := by
  rw [extendPoint, AlgHom.mapValue_apply]

/-- Evaluation of an extended point is obtained by applying the value algebra's structure map. -/
@[simp]
theorem extendPoint_ofConv_apply (H : Type v) [Semiring H] [_root_.HopfAlgebra R H]
    (A : CommAlgCat.{w} R) (g : points (H := H) (CommAlgCat.of R R)) (h : H) :
    (extendPoint H A g).ofConv h = algebraMap R A (g.ofConv h) := by
  simp only [extendPoint, AlgHom.mapValue_apply, WithConv.ofConv_toConv, AlgHom.comp_apply,
    Algebra.ofId_apply]

/-- Extending a ground-ring-valued point back to the ground ring leaves it unchanged. -/
@[simp]
theorem extendPoint_self (H : Type v) [Semiring H] [_root_.HopfAlgebra R H]
    (g : points (H := H) (CommAlgCat.of R R)) :
    extendPoint H (CommAlgCat.of R R) g = g := by
  apply WithConv.ofConv_injective
  ext h
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
    extendPoint_ofConv_apply H (CommAlgCat.of R R) g h

/-- Post-composition of an extended point is extension to the target algebra. -/
theorem mapValue_extendPoint (H : Type v) [Semiring H] [_root_.HopfAlgebra R H]
    {A : CommAlgCat.{w} R} {B : CommAlgCat.{x} R} (f : A →ₐ[R] B)
    (g : points (H := H) (CommAlgCat.of R R)) :
    AlgHom.mapValue (H := H) f (extendPoint H A g) = extendPoint H B g := by
  rw [extendPoint, extendPoint, ← MonoidHom.comp_apply, ← AlgHom.mapValue_comp,
    Algebra.comp_ofId]

/-- The group homomorphism on points induced by a morphism of value algebras.

It sends an `A`-point `f : H →ₐ[R] A` to the `B`-point `φ ∘ f`. The generic lemmas
`map_one`, `map_mul`, and `map_inv` express preservation of the group operations. -/
@[expose] noncomputable def mapPoints {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    points (H := H) A ⟶ points (H := H) B :=
  GrpCat.ofHom (AlgHom.mapValue (H := H) φ.hom)

/-- On points, `mapPoints` is post-composition with the algebra homomorphism `φ`. -/
@[simp]
lemma mapPoints_apply {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f : points (H := H) A) :
    mapPoints (H := H) φ f = toConv (φ.hom.comp f.ofConv) :=
  AlgHom.mapValue_apply φ.hom f

/-- `mapPoints` preserves identity morphisms of value algebras. -/
@[simp]
lemma mapPoints_id (A : CommAlgCat.{w} R) :
    mapPoints (H := H) (𝟙 A) = 𝟙 (points (H := H) A) := by
  simp only [mapPoints, CommAlgCat.hom_id, AlgHom.mapValue_id, GrpCat.ofHom_id]

/-- `mapPoints` preserves composition of morphisms of value algebras. -/
lemma mapPoints_comp {A B C : CommAlgCat.{w} R} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapPoints (H := H) (φ ≫ ψ) = mapPoints (H := H) φ ≫ mapPoints (H := H) ψ := by
  simp only [mapPoints, CommAlgCat.hom_comp, AlgHom.mapValue_comp, GrpCat.ofHom_comp]

/-- The categorical point map sends an extended point to its extension in the target algebra. -/
@[simp]
theorem mapPoints_extendPoint {A B : CommAlgCat.{w} R} (f : A ⟶ B)
    (g : points (H := H) (CommAlgCat.of R R)) :
    mapPoints (H := H) f (extendPoint H A g) = extendPoint H B g :=
  mapValue_extendPoint H f.hom g

/-- The functor of points of a Hopf algebra; when `H` is commutative, it is the functor of points
of the affine group scheme `H` represents.

It maps a commutative `R`-algebra `A` to the convolution group on algebra homomorphisms
`H →ₐ[R] A`, and maps `φ : A ⟶ B` to post-composition with `φ`. -/
@[expose] noncomputable def pointsFunctor : CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := points (H := H) A
  map φ := mapPoints (H := H) φ
  map_id A := mapPoints_id (H := H) A
  map_comp φ ψ := mapPoints_comp (H := H) φ ψ

/-- Natural transformations between points functors agree if they agree on every point. -/
@[ext]
theorem pointsFunctor_hom_ext {K : Type v} [Semiring K] [_root_.HopfAlgebra R K]
    {α β : pointsFunctor (H := H) ⟶ pointsFunctor (H := K)}
    (h : ∀ (A : CommAlgCat.{w} R) (x : points (H := H) A), α.app A x = β.app A x) :
    α = β := by
  apply NatTrans.ext
  funext A
  exact GrpCat.ext (h A)

/-- The object part of `pointsFunctor` is the convolution group of algebra homomorphisms. -/
lemma pointsFunctor_obj (A : CommAlgCat.{w} R) :
    (pointsFunctor (H := H)).obj A = GrpCat.of (WithConv (H →ₐ[R] A)) :=
  rfl

/-- The morphism part of `pointsFunctor` is post-composition in the value algebra. -/
lemma pointsFunctor_map {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (pointsFunctor (H := H)).map φ = mapPoints (H := H) φ :=
  rfl

/-- The map of `pointsFunctor`, transported along its concrete object presentations, is the
corresponding map on points. -/
lemma pointsFunctor_map_eqToHom {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    eqToHom (pointsFunctor_obj (H := H) A).symm ≫
        (pointsFunctor (H := H)).map φ =
      mapPoints (H := H) φ ≫ eqToHom (pointsFunctor_obj (H := H) B).symm :=
  rfl

/-- The pointwise value of the image of an `A`-point under `pointsFunctor.map φ`. -/
@[simp]
lemma pointsFunctor_map_apply_apply {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f : WithConv (H →ₐ[R] A)) (h : H) :
    (((pointsFunctor (H := H)).map φ f : WithConv (H →ₐ[R] B)).ofConv) h =
      φ.hom (f.ofConv h) := by
  erw [pointsFunctor_map, mapPoints_apply]
  rw [WithConv.ofConv_toConv, AlgHom.comp_apply]

/-- The group-valued functor of a family of point subgroups stable under change of value
algebra: every value-algebra morphism `φ : A ⟶ B` maps `S A` into `S B`, and the functor acts on
`S A` by the restriction of the point map. -/
@[expose] noncomputable def subgroupFunctor
    (S : (A : CommAlgCat.{w} R) → Subgroup (points (H := H) A))
    (hS : ∀ {A B : CommAlgCat.{w} R} (φ : A ⟶ B),
      S A ≤ (S B).comap (AlgHom.mapValue (H := H) φ.hom)) :
    CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := GrpCat.of (S A)
  map {A B} φ := GrpCat.ofHom
    (((AlgHom.mapValue (H := H) φ.hom).domRestrict (S A)).codRestrict (S B) fun g ↦ hS φ g.2)
  map_id A := GrpCat.ext fun g ↦ Subtype.ext <| by
    simp only [CommAlgCat.hom_id, AlgHom.mapValue_id]
    rfl
  map_comp φ ψ := GrpCat.ext fun g ↦ Subtype.ext <| by
    simp only [CommAlgCat.hom_comp, AlgHom.mapValue_comp]
    rfl

/-- The object part of a point-subgroup functor is the specified subgroup. -/
@[simp]
lemma subgroupFunctor_obj
    (S : (A : CommAlgCat.{w} R) → Subgroup (points (H := H) A))
    (hS : ∀ {A B : CommAlgCat.{w} R} (φ : A ⟶ B),
      S A ≤ (S B).comap (AlgHom.mapValue (H := H) φ.hom))
    (A : CommAlgCat.{w} R) :
    (subgroupFunctor (H := H) S hS).obj A = GrpCat.of (S A) :=
  rfl

/-- The map part of a point-subgroup functor is the restriction of the point map. -/
@[simp]
lemma subgroupFunctor_map
    (S : (A : CommAlgCat.{w} R) → Subgroup (points (H := H) A))
    (hS : ∀ {A B : CommAlgCat.{w} R} (φ : A ⟶ B),
      S A ≤ (S B).comap (AlgHom.mapValue (H := H) φ.hom))
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (subgroupFunctor (H := H) S hS).map φ = GrpCat.ofHom
      (((AlgHom.mapValue (H := H) φ.hom).domRestrict (S A)).codRestrict (S B)
        fun g ↦ hS φ g.2) :=
  rfl

/-- The inclusion of a stable family of point subgroups into the functor of points is natural. -/
noncomputable def subgroupFunctorIncl
    (S : (A : CommAlgCat.{w} R) → Subgroup (points (H := H) A))
    (hS : ∀ {A B : CommAlgCat.{w} R} (φ : A ⟶ B),
      S A ≤ (S B).comap (AlgHom.mapValue (H := H) φ.hom)) :
    subgroupFunctor (H := H) S hS ⟶ pointsFunctor (H := H) where
  app A := GrpCat.ofHom (S A).subtype
  naturality _ _ _ := rfl

/-- The component of the inclusion of a point-subgroup functor is the subgroup inclusion. -/
@[simp]
lemma subgroupFunctorIncl_app
    (S : (A : CommAlgCat.{w} R) → Subgroup (points (H := H) A))
    (hS : ∀ {A B : CommAlgCat.{w} R} (φ : A ⟶ B),
      S A ≤ (S B).comap (AlgHom.mapValue (H := H) φ.hom))
    (A : CommAlgCat.{w} R) :
    (subgroupFunctorIncl (H := H) S hS).app A = GrpCat.ofHom (S A).subtype :=
  (rfl)

end HopfAlgebra

end MathlibExt
