/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder

/-!
# Exact functorial cylinders

A functorial cylinder uses the existing precylinder of the identity
endofunctor. Its application uses the natural transformation components
to give a native precylinder at each object. Exactness records monic pointwise
boundaries, preservation of small colimits and monomorphisms, and the
endpoint pullback squares along monomorphisms.

The colimit size is an explicit universe. The definitions apply to any
category with binary coproducts. In a category of presheaves valued in
Type u, that size is u. The presheaf union and corner monomorphism results
use the additional properties of presheaf categories.

This is the datum in Cisinski, Higher Categories and Homotopical Algebra,
Definitions 2.4.6 and 2.4.8, July 30, 2026 version. No weak-equivalence
predicate is required for the precylinder or its exactness property.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe w v u v' u'

namespace HomotopicalAlgebra.Precylinder

section Endpoints

variable {C : Type u} [Category.{v} C] {A : C}

/-- The first and second endpoints of a native precylinder. -/
def endpoint (P : Precylinder A) (ε : Fin 2) : A ⟶ P.I :=
  Fin.cases P.i₀ (fun _ ↦ P.i₁) ε

@[simp]
lemma endpoint_zero (P : Precylinder A) : P.endpoint 0 = P.i₀ := rfl

@[simp]
lemma endpoint_one (P : Precylinder A) : P.endpoint 1 = P.i₁ := rfl

@[reassoc (attr := simp)]
lemma endpoint_π (P : Precylinder A) (ε : Fin 2) :
    P.endpoint ε ≫ P.π = 𝟙 A := by
  refine Fin.cases ?_ (fun _ ↦ ?_) ε
  · exact P.i₀_π
  · exact P.i₁_π

/-- Each endpoint is a section and therefore a monomorphism. -/
instance mono_endpoint (P : Precylinder A) (ε : Fin 2) : Mono (P.endpoint ε) := by
  refine ⟨fun f g h ↦ ?_⟩
  have h' := congrArg (fun k ↦ k ≫ P.π) h
  simpa only [Category.assoc, endpoint_π, Category.comp_id] using h'

@[simp]
lemma map_endpoint (P : Precylinder A) {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) (ε : Fin 2) : (P.map F).endpoint ε = F.map (P.endpoint ε) := by
  refine Fin.cases ?_ (fun _ ↦ ?_) ε <;> rfl

end Endpoints

section Functorial

variable {C : Type u} [Category.{v} C]

/-- Evaluate a precylinder of the identity functor at an object. -/
@[simps I i₀ i₁ π]
abbrev app (P : Precylinder (𝟭 C)) (X : C) : Precylinder X :=
  { I := P.I.obj X
    i₀ := P.i₀.app X
    i₁ := P.i₁.app X
    π := P.π.app X
    i₀_π := NatTrans.congr_app P.i₀_π X
    i₁_π := NatTrans.congr_app P.i₁_π X }

@[simp]
lemma app_endpoint (P : Precylinder (𝟭 C)) (X : C) (ε : Fin 2) :
    (P.app X).endpoint ε = (P.endpoint ε).app X := by
  refine Fin.cases ?_ (fun _ ↦ ?_) ε <;> rfl

@[reassoc]
lemma endpoint_naturality (P : Precylinder (𝟭 C)) {X Y : C} (i : X ⟶ Y)
    (ε : Fin 2) :
    i ≫ (P.app Y).endpoint ε = (P.app X).endpoint ε ≫ P.I.map i := by
  simpa only [app_endpoint, Functor.id_map] using (P.endpoint ε).naturality i

variable [HasBinaryCoproducts C]

/-- The boundary map of the pointwise native precylinder is natural. -/
@[reassoc]
lemma boundary_naturality (P : Precylinder (𝟭 C)) {X Y : C} (i : X ⟶ Y) :
    coprod.map i i ≫ (P.app Y).i = (P.app X).i ≫ P.I.map i := by
  apply coprod.hom_ext
  · rw [coprod.inl_map_assoc, inl_i, ← Category.assoc, inl_i]
    exact P.i₀.naturality i
  · rw [coprod.inr_map_assoc, inr_i, ← Category.assoc, inr_i]
    exact P.i₁.naturality i

/-- Exactness at the selected colimit size: the pointwise boundary is
monic, the endofunctor preserves monomorphisms and small colimits, and
each endpoint naturality square along a monomorphism is a pullback. -/
class IsExact (P : Precylinder (𝟭 C)) : Prop extends
    Functor.PreservesMonomorphisms P.I, PreservesColimitsOfSize.{w, w} P.I where
  /-- The two pointwise endpoints have a monic coproduct map. -/
  mono_boundary (X : C) : Mono (P.app X).i
  /-- The endpoint square along a monomorphism is a pullback. -/
  endpoint_isPullback {X Y : C} (i : X ⟶ Y) [Mono i] (ε : Fin 2) :
    IsPullback i ((P.app X).endpoint ε) ((P.app Y).endpoint ε) (P.I.map i)

instance mono_app_i (P : Precylinder (𝟭 C)) [P.IsExact.{w}] (X : C) :
    Mono (P.app X).i :=
  IsExact.mono_boundary X

end Functorial

section Corners

variable {C : Type u} [Category.{v} C] (P : Precylinder (𝟭 C)) {X Y : C}

/-- The endpoint corner map from its specified pushout. -/
noncomputable def endpointCorner (i : X ⟶ Y) (ε : Fin 2)
    [HasPushout i ((P.app X).endpoint ε)] :
    pushout i ((P.app X).endpoint ε) ⟶ P.I.obj Y :=
  pushout.desc ((P.app Y).endpoint ε) (P.I.map i) (P.endpoint_naturality i ε)

@[reassoc (attr := simp)]
lemma inl_endpointCorner (i : X ⟶ Y) (ε : Fin 2)
    [HasPushout i ((P.app X).endpoint ε)] :
    pushout.inl i ((P.app X).endpoint ε) ≫ P.endpointCorner i ε =
      (P.app Y).endpoint ε := by
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_endpointCorner (i : X ⟶ Y) (ε : Fin 2)
    [HasPushout i ((P.app X).endpoint ε)] :
    pushout.inr i ((P.app X).endpoint ε) ≫ P.endpointCorner i ε = P.I.map i := by
  exact pushout.inr_desc _ _ _

variable [HasBinaryCoproducts C]

/-- The boundary corner map from its specified pushout. -/
noncomputable def boundaryCorner (i : X ⟶ Y)
    [HasPushout (coprod.map i i) (P.app X).i] :
    pushout (coprod.map i i) (P.app X).i ⟶ P.I.obj Y :=
  pushout.desc (P.app Y).i (P.I.map i) (P.boundary_naturality i)

@[reassoc (attr := simp)]
lemma inl_boundaryCorner (i : X ⟶ Y)
    [HasPushout (coprod.map i i) (P.app X).i] :
    pushout.inl (coprod.map i i) (P.app X).i ≫ P.boundaryCorner i = (P.app Y).i := by
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_boundaryCorner (i : X ⟶ Y)
    [HasPushout (coprod.map i i) (P.app X).i] :
    pushout.inr (coprod.map i i) (P.app X).i ≫ P.boundaryCorner i = P.I.map i := by
  exact pushout.inr_desc _ _ _

end Corners

end HomotopicalAlgebra.Precylinder
