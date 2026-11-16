/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Source port of TauCeti/Algebra/AlgebraicGroup/CommHopfAlgCat/Basic.lean.
TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Modifications: change only project namespaces and import paths.
The original Apache 2.0 copyright and authors above are retained.
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import MathlibExt.Algebra.AlgebraicGroup.Hopf.Map
public import MathlibExt.Algebra.AlgebraicGroup.PointsFunctor

/-!
# Commutative Hopf algebras and their functor of points

This file packages the group object represented by a commutative coordinate Hopf algebra and the
contravariant functor that sends it to its group-valued functor of points `A ↦ Hom_R(H, A)`.

The category of commutative Hopf algebras is Mathlib's bundled `CommHopfAlgCat`; this file
adds the functor-of-points stack on top of it.

For a commutative Hopf algebra representing an affine group scheme, the functor of points
is group-valued by convolution, and a morphism of coordinate Hopf algebras acts on points
by pre-composition.

## Main declarations

* `CommHopfAlgCat.Hom.mapPointsFunctor`: a coordinate morphism `H ⟶ K` induces a natural
  transformation from the points functor of `K` to the points functor of `H`.
* `CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply`: pointwise contravariance under composition
  of coordinate morphisms.
* `MathlibExt.CommHopfAlgCat.pointsFunctor`: the contravariant functor
  `(CommHopfAlgCat R)ᵒᵖ ⥤ CommAlgCat R ⥤ GrpCat`.
* `CommHopfAlgCat.grpObj`: the underlying object of the represented group object.
* `CommHopfAlgCat.Hom.grpObjMap`: the contravariant morphism of represented group objects
  induced by a coordinate Hopf-algebra morphism.
* `CommHopfAlgCat.Hom.whiskerLeft_grpObjMap_unop_hom`: the coordinate description of left whiskering
  a represented group-object map.
* `CommHopfAlgCat.Hom.grpObjMap_injective`: represented group-object maps determine their coordinate
  Hopf-algebra morphisms.
* `CommHopfAlgCat.coe_ofIso`: the bialgebra equivalence of an isomorphism has the forward
  morphism as its underlying bialgebra morphism.

## See also

* `Mathlib.Algebra.Category.CommHopfAlgCat`: the bundled category `CommHopfAlgCat`, its forgetful
  functor to `CommBialgCat`, and the equivalence `commHopfAlgCatEquivCogrpCommAlgCat`.
* `Mathlib.RingTheory.Bialgebra.Convolution`: convolution monoid and bialgebra morphism API,
  in particular `AlgHom.convMul_comp_bialgHom_distrib`.
* `MathlibExt.Algebra.AlgebraicGroup.Hopf.Map`: the `BialgHom.mapDomain` wrapper.
-/

public section

open CategoryTheory Opposite WithConv

namespace MathlibExt

universe u v w

namespace CommHopfAlgCat

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

variable {R : Type u} [CommRing R]

/-- The underlying object `op (CommAlgCat.of R H)` of the group object represented by the
commutative Hopf algebra `H`, carrying the induced `GrpObj` structure. -/
noncomputable abbrev _root_.CommHopfAlgCat.grpObj (H : _root_.CommHopfAlgCat.{u} R) :
    (CommAlgCat.{u} R)ᵒᵖ :=
  op (CommAlgCat.of R H)

/-- The morphism of underlying group objects represented contravariantly by a morphism of
commutative Hopf algebras. -/
noncomputable def _root_.CommHopfAlgCat.Hom.grpObjMap
    {H K : _root_.CommHopfAlgCat.{u} R} (f : H ⟶ K) :
    grpObj K ⟶ grpObj H :=
  (CommAlgCat.ofHom f.hom).op

/-- Unopping `grpObjMap f` gives the underlying commutative-algebra morphism of `f`. -/
@[simp]
theorem _root_.CommHopfAlgCat.Hom.grpObjMap_unop {H K : _root_.CommHopfAlgCat.{u} R} (f : H ⟶ K) :
    (grpObjMap f).unop = CommAlgCat.ofHom f.hom := (rfl)

/-- The underlying algebra homomorphism obtained by unopping `grpObjMap f` is the underlying
algebra homomorphism of `f`. -/
theorem _root_.CommHopfAlgCat.Hom.grpObjMap_unop_hom
    {H K : _root_.CommHopfAlgCat.{u} R} (f : H ⟶ K) :
    (grpObjMap f).unop.hom = f.hom.toAlgHom :=
  congrArg CommAlgCat.Hom.hom (grpObjMap_unop f)

/-- Unopping the left whiskering of a represented group-object map gives the tensor product of
the identity with its underlying coordinate algebra map. -/
theorem _root_.CommHopfAlgCat.Hom.whiskerLeft_grpObjMap_unop_hom
    {H K : _root_.CommHopfAlgCat.{u} R} (f : H ⟶ K) :
    (MonoidalCategoryStruct.whiskerLeft (grpObj H) (grpObjMap f)).unop.hom =
      Algebra.TensorProduct.map (AlgHom.id R H) f.hom.toAlgHom := by
  simp only [unop_whiskerLeft, CommAlgCat.whiskerLeft_hom, grpObjMap_unop_hom]

/-- Represented group-object maps determine their coordinate Hopf-algebra morphisms. -/
theorem _root_.CommHopfAlgCat.Hom.grpObjMap_injective {H K : _root_.CommHopfAlgCat.{u} R} :
    Function.Injective (grpObjMap : (H ⟶ K) → (grpObj K ⟶ grpObj H)) := by
  intro f g h
  apply _root_.CommHopfAlgCat.hom_ext
  apply BialgHom.ext
  intro x
  simpa only [grpObjMap_unop_hom, BialgHom.coe_toAlgHom] using
    congrArg (fun q ↦ q.unop.hom x) h

/-- The identity coordinate morphism represents the identity group-object morphism. -/
@[simp]
theorem _root_.CommHopfAlgCat.Hom.grpObjMap_id (H : _root_.CommHopfAlgCat.{u} R) :
    grpObjMap (𝟙 H) = 𝟙 (grpObj H) := by
  rfl

/-- Composition of coordinate morphisms is represented contravariantly. -/
@[simp]
theorem _root_.CommHopfAlgCat.Hom.grpObjMap_comp
    {H K L : _root_.CommHopfAlgCat.{u} R} (f : H ⟶ K) (g : K ⟶ L) :
    grpObjMap (f ≫ g) = grpObjMap g ≫ grpObjMap f := by
  rfl

/-- The bialgebra equivalence underlying an isomorphism of commutative Hopf algebras has the
forward morphism of the isomorphism as its underlying bialgebra morphism. -/
theorem coe_ofIso {H K : _root_.CommHopfAlgCat.{u} R} (e : H ≅ K) :
    ((_root_.CommHopfAlgCat.ofIso e : H ≃ₐc[R] K) : H →ₐc[R] K) = e.hom.hom :=
  (rfl)

/-- A morphism represented by a commutative Hopf-algebra morphism preserves the group-object
multiplication. -/
noncomputable instance _root_.CommHopfAlgCat.Hom.grpObjMap_isMonHom
    {H K : _root_.CommHopfAlgCat.{u} R} (f : H ⟶ K) :
    IsMonHom (grpObjMap f) := by
  -- `grpObjMap` uses the concrete opposite-algebra spelling, whereas Mathlib registers the
  -- `IsMonHom` instance on the definitionally equal morphism transported by the equivalence.
  change IsMonHom (((commHopfAlgCatEquivCogrpCommAlgCat R).functor.map f).unop.hom.hom)
  infer_instance

/-- A morphism of coordinate commutative Hopf algebras induces a natural transformation
between their group-valued points functors, contravariantly in the coordinate algebra.

At a commutative `R`-algebra `A`, this sends an `A`-valued point `f : K →ₐ[R] A` to
`f ∘ φ : H →ₐ[R] A`. -/
@[expose] noncomputable def _root_.CommHopfAlgCat.Hom.mapPointsFunctor
    {H K : CommHopfAlgCat.{v} R} (φ : H ⟶ K) :
    HopfAlgebra.pointsFunctor (R := R) (H := K) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := H) where
  app A := GrpCat.ofHom
    (BialgHom.mapDomain (H₁ := H) (H₂ := K) (A := A) φ.hom)
  naturality {A B} ψ := by
    simp only [HopfAlgebra.pointsFunctor_map, HopfAlgebra.mapPoints]
    exact GrpCat.hom_ext (BialgHom.mapValue_mapDomain φ.hom ψ.hom)

/-- On points, `mapPointsFunctor φ` is pre-composition with `φ`. -/
@[simp]
lemma _root_.CommHopfAlgCat.Hom.mapPointsFunctor_app_apply {H K : CommHopfAlgCat.{v} R} (φ : H ⟶ K)
    (A : CommAlgCat.{w} R) (f : HopfAlgebra.points (R := R) (H := K) A) :
    (mapPointsFunctor φ).app A f =
      toConv (f.ofConv.comp (φ.hom : H →ₐ[R] K)) := by
  exact BialgHom.mapDomain_apply (A := A) φ.hom f

/-- Pointwise form of `mapPointsFunctor_app_apply`. -/
lemma _root_.CommHopfAlgCat.Hom.mapPointsFunctor_app_apply_apply
    {H K : CommHopfAlgCat.{v} R} (φ : H ⟶ K)
    (A : CommAlgCat.{w} R) (f : HopfAlgebra.points (R := R) (H := K) A) (h : H) :
    (((mapPointsFunctor φ).app A f).ofConv) h = f.ofConv (φ.hom h) := by
  exact BialgHom.mapDomain_apply_apply (A := A) φ.hom f h

/-- Naturality of the point map induced by a coordinate morphism, applied to a point. -/
lemma _root_.CommHopfAlgCat.Hom.mapPointsFunctor_naturality_apply
    {H K : CommHopfAlgCat.{v} R} (φ : H ⟶ K)
    {A B : CommAlgCat.{w} R} (χ : A ⟶ B)
    (f : HopfAlgebra.points (R := R) (H := K) A) :
    HopfAlgebra.mapPoints (H := H) χ ((mapPointsFunctor φ).app A f) =
      (mapPointsFunctor φ).app B (HopfAlgebra.mapPoints (H := K) χ f) := by
  exact DFunLike.congr_fun (BialgHom.mapValue_mapDomain φ.hom χ.hom).symm f

/-- Pre-composition with a surjective coordinate morphism is injective on points. -/
lemma _root_.CommHopfAlgCat.Hom.mapPointsFunctor_app_injective_of_surjective
    {H K : CommHopfAlgCat.{v} R}
    (φ : H ⟶ K) (hφ : Function.Surjective φ.hom) (A : CommAlgCat.{w} R) :
    Function.Injective ((mapPointsFunctor φ).app A) :=
  BialgHom.mapDomain_injective_of_surjective (A := A) φ.hom hφ

/-- `mapPointsFunctor` sends the identity coordinate morphism to the identity natural
transformation. -/
@[simp]
lemma _root_.CommHopfAlgCat.Hom.mapPointsFunctor_id (H : CommHopfAlgCat.{v} R) :
    mapPointsFunctor (𝟙 H) =
      𝟙 (HopfAlgebra.pointsFunctor (R := R) (H := H) :
        CommAlgCat.{w} R ⥤ GrpCat.{max v w}) := by
  ext A f
  -- The `GrpCat.ofHom` component and `(𝟙 H).hom` hide the bialgebra identity
  -- expected by `mapDomain_id`; reduce those categorical wrappers while keeping
  -- `BialgHom.mapDomain` opaque.
  change BialgHom.mapDomain (BialgHom.id R H) f = f
  rw [BialgHom.mapDomain_id]
  rfl

/-- `mapPointsFunctor` sends coordinate-algebra composition to reverse composition of natural
transformations. -/
lemma _root_.CommHopfAlgCat.Hom.mapPointsFunctor_comp
    {H K L : CommHopfAlgCat.{v} R} (φ : H ⟶ K) (ψ : K ⟶ L) :
    mapPointsFunctor (φ ≫ ψ) =
      mapPointsFunctor ψ ≫ mapPointsFunctor φ := by
  ext A f
  -- Natural-transformation composition packages the point maps as `GrpCat.ofHom`,
  -- and `(φ ≫ ψ).hom` uses `CommHopfAlgCat` composition. Reduce those wrappers to
  -- expose the bialgebra composition expected by `mapDomain_comp`.
  change BialgHom.mapDomain (ψ.hom.comp φ.hom) f =
    BialgHom.mapDomain φ.hom (BialgHom.mapDomain ψ.hom f)
  rw [BialgHom.mapDomain_comp, MonoidHom.comp_apply]

/-- Pointwise form of contravariance of `mapPointsFunctor` under composition. -/
lemma _root_.CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply {H K L : CommHopfAlgCat.{v} R}
    (φ : H ⟶ K) (ψ : K ⟶ L) (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := L) A) :
    (mapPointsFunctor (φ ≫ ψ)).app A f =
      (mapPointsFunctor φ).app A ((mapPointsFunctor ψ).app A f) := by
  rw [mapPointsFunctor_comp, NatTrans.comp_app]
  exact GrpCat.comp_apply ((mapPointsFunctor ψ).app A) ((mapPointsFunctor φ).app A) f

/-- The contravariant functor assigning to a commutative Hopf algebra its group-valued
functor of points.

A coordinate Hopf algebra `H` is sent to the functor `A ↦ WithConv (H →ₐ[R] A)`. A morphism
`φ : H ⟶ K` is sent contravariantly to the natural transformation that pre-composes
`K`-points by `φ`. -/
@[expose] noncomputable def pointsFunctor :
    (CommHopfAlgCat.{v} R)ᵒᵖ ⥤ CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj H := HopfAlgebra.pointsFunctor (R := R) (H := H.unop)
  map φ := CommHopfAlgCat.Hom.mapPointsFunctor φ.unop
  map_id H := CommHopfAlgCat.Hom.mapPointsFunctor_id (R := R) H.unop
  map_comp φ ψ := CommHopfAlgCat.Hom.mapPointsFunctor_comp (R := R) ψ.unop φ.unop

/-- The object part of `pointsFunctor` is the points functor of the underlying commutative
Hopf algebra. -/
lemma pointsFunctor_obj (H : (CommHopfAlgCat.{v} R)ᵒᵖ) :
    (pointsFunctor (R := R)).obj H =
      HopfAlgebra.pointsFunctor (R := R) (H := H.unop) :=
  rfl

/-- The morphism part of `pointsFunctor` is pre-composition in the coordinate commutative
Hopf algebra. -/
lemma pointsFunctor_map {H K : (CommHopfAlgCat.{v} R)ᵒᵖ} (φ : H ⟶ K) :
    (pointsFunctor (R := R)).map φ =
      CommHopfAlgCat.Hom.mapPointsFunctor φ.unop :=
  rfl

/-- Pointwise form of the morphism part of `pointsFunctor`. -/
@[simp]
lemma pointsFunctor_map_app_apply_apply {H K : (CommHopfAlgCat.{v} R)ᵒᵖ}
    (φ : H ⟶ K) (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := H.unop) A) (h : K.unop) :
    ((((pointsFunctor (R := R)).map φ).app A f).ofConv) h =
      f.ofConv (φ.unop.hom h) := by
  rw [pointsFunctor_map]
  exact CommHopfAlgCat.Hom.mapPointsFunctor_app_apply_apply (R := R) φ.unop A f h

end CommHopfAlgCat

end MathlibExt
