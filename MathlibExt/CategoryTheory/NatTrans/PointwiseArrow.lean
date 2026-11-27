/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Natural transformations as pointwise arrow functors

A natural transformation determines a functor to an arrow category.  When the
target is itself a functor category, this file also provides the pointwise
version whose two indexing categories remain visible.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace NatTrans

variable {B : Type u₁} [Category.{v₁} B]
variable {I : Type u₂} [Category.{v₂} I]
variable {C : Type u₃} [Category.{v₃} C]

/-- A natural transformation, regarded as a functor to the arrow category. -/
def arrow {F G : B ⥤ C} (α : F ⟶ G) : B ⥤ Arrow C where
  obj b := Arrow.mk (α.app b)
  map f := Arrow.homMk (F.map f) (G.map f) (α.naturality f)
  map_id b := by
    apply Arrow.hom_ext
    · exact F.map_id b
    · exact G.map_id b
  map_comp f g := by
    apply Arrow.hom_ext
    · exact F.map_comp f g
    · exact G.map_comp f g

@[simp]
lemma arrow_obj {F G : B ⥤ C} (α : F ⟶ G) (b : B) :
    (arrow α).obj b = Arrow.mk (α.app b) :=
  rfl

@[simp]
lemma arrow_obj_left {F G : B ⥤ C} (α : F ⟶ G) (b : B) :
    ((arrow α).obj b).left = F.obj b :=
  rfl

@[simp]
lemma arrow_obj_right {F G : B ⥤ C} (α : F ⟶ G) (b : B) :
    ((arrow α).obj b).right = G.obj b :=
  rfl

@[simp]
lemma arrow_obj_hom {F G : B ⥤ C} (α : F ⟶ G) (b : B) :
    ((arrow α).obj b).hom = α.app b :=
  rfl

@[simp]
lemma arrow_map_left {F G : B ⥤ C} (α : F ⟶ G) {b b' : B} (f : b ⟶ b') :
    ((arrow α).map f).left = F.map f :=
  rfl

@[simp]
lemma arrow_map_right {F G : B ⥤ C} (α : F ⟶ G) {b b' : B} (f : b ⟶ b') :
    ((arrow α).map f).right = G.map f :=
  rfl

lemma arrow_map {F G : B ⥤ C} (α : F ⟶ G) {b b' : B} (f : b ⟶ b') :
    (arrow α).map f = Arrow.homMk (F.map f) (G.map f) (α.naturality f) :=
  rfl

/-- The functor of pointwise arrows associated to a natural transformation
between functors valued in a functor category. -/
def pointwiseArrow {F G : B ⥤ I ⥤ C} (α : F ⟶ G) : B ⥤ I ⥤ Arrow C where
  obj b := arrow (α.app b)
  map {b b'} f :=
    { app := fun i ↦
        Arrow.homMk ((F.map f).app i) ((G.map f).app i)
          (congr_app (α.naturality f) i)
      naturality := by
        intro i i' g
        apply Arrow.hom_ext
        · exact (F.map f).naturality g
        · exact (G.map f).naturality g }
  map_id b := by
    apply NatTrans.ext
    funext i
    apply Arrow.hom_ext <;> simp
  map_comp f g := by
    apply NatTrans.ext
    funext i
    apply Arrow.hom_ext <;> simp

@[simp]
lemma pointwiseArrow_obj_obj {F G : B ⥤ I ⥤ C} (α : F ⟶ G) (b : B) (i : I) :
    ((pointwiseArrow α).obj b).obj i = Arrow.mk ((α.app b).app i) :=
  rfl

@[simp]
lemma pointwiseArrow_obj_obj_left {F G : B ⥤ I ⥤ C} (α : F ⟶ G) (b : B) (i : I) :
    (((pointwiseArrow α).obj b).obj i).left = (F.obj b).obj i :=
  rfl

@[simp]
lemma pointwiseArrow_obj_obj_right {F G : B ⥤ I ⥤ C} (α : F ⟶ G) (b : B) (i : I) :
    (((pointwiseArrow α).obj b).obj i).right = (G.obj b).obj i :=
  rfl

@[simp]
lemma pointwiseArrow_obj_obj_hom {F G : B ⥤ I ⥤ C} (α : F ⟶ G) (b : B) (i : I) :
    (((pointwiseArrow α).obj b).obj i).hom = (α.app b).app i :=
  rfl

@[simp]
lemma pointwiseArrow_obj_map_left {F G : B ⥤ I ⥤ C} (α : F ⟶ G) (b : B)
    {i i' : I} (f : i ⟶ i') :
    (((pointwiseArrow α).obj b).map f).left = (F.obj b).map f :=
  rfl

@[simp]
lemma pointwiseArrow_obj_map_right {F G : B ⥤ I ⥤ C} (α : F ⟶ G) (b : B)
    {i i' : I} (f : i ⟶ i') :
    (((pointwiseArrow α).obj b).map f).right = (G.obj b).map f :=
  rfl

lemma pointwiseArrow_obj_map {F G : B ⥤ I ⥤ C} (α : F ⟶ G) (b : B)
    {i i' : I} (f : i ⟶ i') :
    ((pointwiseArrow α).obj b).map f =
      Arrow.homMk ((F.obj b).map f) ((G.obj b).map f) ((α.app b).naturality f) :=
  rfl

@[simp]
lemma pointwiseArrow_map_app_left {F G : B ⥤ I ⥤ C} (α : F ⟶ G) {b b' : B}
    (f : b ⟶ b') (i : I) :
    (((pointwiseArrow α).map f).app i).left = (F.map f).app i :=
  rfl

@[simp]
lemma pointwiseArrow_map_app_right {F G : B ⥤ I ⥤ C} (α : F ⟶ G) {b b' : B}
    (f : b ⟶ b') (i : I) :
    (((pointwiseArrow α).map f).app i).right = (G.map f).app i :=
  rfl

lemma pointwiseArrow_map_app {F G : B ⥤ I ⥤ C} (α : F ⟶ G) {b b' : B}
    (f : b ⟶ b') (i : I) :
    ((pointwiseArrow α).map f).app i =
      Arrow.homMk ((F.map f).app i) ((G.map f).app i)
        (congr_app (α.naturality f) i) :=
  rfl

/-- The pointwise arrow isomorphism induced by commuting endpoint isomorphisms. -/
def arrowFunctorIso
    {C D : Type*} [Category C] [Category D] {F G F' G' : C ⥤ D}
    (η : F ⟶ G) (θ : F' ⟶ G')
    (a : ∀ X : C, F.obj X ≅ F'.obj X) (b : ∀ X : C, G.obj X ≅ G'.obj X)
    (ha : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (a Y).hom = (a X).hom ≫ F'.map f)
    (hb : ∀ {X Y : C} (f : X ⟶ Y), G.map f ≫ (b Y).hom = (b X).hom ≫ G'.map f)
    (hs : ∀ X : C, (a X).hom ≫ θ.app X = η.app X ≫ (b X).hom) :
    CategoryTheory.NatTrans.arrow η ≅ CategoryTheory.NatTrans.arrow θ :=
  NatIso.ofComponents
    (fun X => CategoryTheory.Arrow.isoMk' (η.app X) (θ.app X) (a X) (b X) (hs X))
    (fun f => by
      apply CategoryTheory.Arrow.hom_ext
      · exact ha f
      · exact hb f)

/-- The natural arrow-functor isomorphism induced by commuting natural endpoint isomorphisms. -/
def arrowFunctorNatIso
    {C D : Type*} [Category C] [Category D] {F G F' G' : C ⥤ D}
    (η : F ⟶ G) (θ : F' ⟶ G') (a : F ≅ F') (b : G ≅ G')
    (hs : ∀ X : C, a.hom.app X ≫ θ.app X = η.app X ≫ b.hom.app X) :
    CategoryTheory.NatTrans.arrow η ≅ CategoryTheory.NatTrans.arrow θ :=
  arrowFunctorIso η θ (fun X => a.app X) (fun X => b.app X)
    (fun f => a.hom.naturality f) (fun f => b.hom.naturality f) hs

/-- The source component of the forward natural arrow isomorphism. -/
@[simp]
theorem arrowFunctorNatIso_hom_left
    {C D : Type*} [Category C] [Category D] {F G F' G' : C ⥤ D}
    (η : F ⟶ G) (θ : F' ⟶ G') (a : F ≅ F') (b : G ≅ G')
    (hs : ∀ X : C, a.hom.app X ≫ θ.app X = η.app X ≫ b.hom.app X) (X : C) :
    ((arrowFunctorNatIso η θ a b hs).hom.app X).left = a.hom.app X := rfl

/-- The target component of the forward natural arrow isomorphism. -/
@[simp]
theorem arrowFunctorNatIso_hom_right
    {C D : Type*} [Category C] [Category D] {F G F' G' : C ⥤ D}
    (η : F ⟶ G) (θ : F' ⟶ G') (a : F ≅ F') (b : G ≅ G')
    (hs : ∀ X : C, a.hom.app X ≫ θ.app X = η.app X ≫ b.hom.app X) (X : C) :
    ((arrowFunctorNatIso η θ a b hs).hom.app X).right = b.hom.app X := rfl

/-- The source component of the inverse natural arrow isomorphism. -/
@[simp]
theorem arrowFunctorNatIso_inv_left
    {C D : Type*} [Category C] [Category D] {F G F' G' : C ⥤ D}
    (η : F ⟶ G) (θ : F' ⟶ G') (a : F ≅ F') (b : G ≅ G')
    (hs : ∀ X : C, a.hom.app X ≫ θ.app X = η.app X ≫ b.hom.app X) (X : C) :
    ((arrowFunctorNatIso η θ a b hs).inv.app X).left = a.inv.app X := rfl

/-- The target component of the inverse natural arrow isomorphism. -/
@[simp]
theorem arrowFunctorNatIso_inv_right
    {C D : Type*} [Category C] [Category D] {F G F' G' : C ⥤ D}
    (η : F ⟶ G) (θ : F' ⟶ G') (a : F ≅ F') (b : G ≅ G')
    (hs : ∀ X : C, a.hom.app X ≫ θ.app X = η.app X ≫ b.hom.app X) (X : C) :
    ((arrowFunctorNatIso η θ a b hs).inv.app X).right = b.inv.app X := rfl

/-- The source component of the forward pointwise arrow isomorphism. -/
@[simp]
theorem arrowFunctorIso_hom_left
    {C D : Type*} [Category C] [Category D] {F G F' G' : C ⥤ D}
    (η : F ⟶ G) (θ : F' ⟶ G')
    (a : ∀ X : C, F.obj X ≅ F'.obj X) (b : ∀ X : C, G.obj X ≅ G'.obj X)
    (ha : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (a Y).hom = (a X).hom ≫ F'.map f)
    (hb : ∀ {X Y : C} (f : X ⟶ Y), G.map f ≫ (b Y).hom = (b X).hom ≫ G'.map f)
    (hs : ∀ X : C, (a X).hom ≫ θ.app X = η.app X ≫ (b X).hom) (X : C) :
    ((arrowFunctorIso η θ a b ha hb hs).hom.app X).left = (a X).hom := rfl

/-- The target component of the forward pointwise arrow isomorphism. -/
@[simp]
theorem arrowFunctorIso_hom_right
    {C D : Type*} [Category C] [Category D] {F G F' G' : C ⥤ D}
    (η : F ⟶ G) (θ : F' ⟶ G')
    (a : ∀ X : C, F.obj X ≅ F'.obj X) (b : ∀ X : C, G.obj X ≅ G'.obj X)
    (ha : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (a Y).hom = (a X).hom ≫ F'.map f)
    (hb : ∀ {X Y : C} (f : X ⟶ Y), G.map f ≫ (b Y).hom = (b X).hom ≫ G'.map f)
    (hs : ∀ X : C, (a X).hom ≫ θ.app X = η.app X ≫ (b X).hom) (X : C) :
    ((arrowFunctorIso η θ a b ha hb hs).hom.app X).right = (b X).hom := rfl

/-- The source component of the inverse pointwise arrow isomorphism. -/
@[simp]
theorem arrowFunctorIso_inv_left
    {C D : Type*} [Category C] [Category D] {F G F' G' : C ⥤ D}
    (η : F ⟶ G) (θ : F' ⟶ G')
    (a : ∀ X : C, F.obj X ≅ F'.obj X) (b : ∀ X : C, G.obj X ≅ G'.obj X)
    (ha : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (a Y).hom = (a X).hom ≫ F'.map f)
    (hb : ∀ {X Y : C} (f : X ⟶ Y), G.map f ≫ (b Y).hom = (b X).hom ≫ G'.map f)
    (hs : ∀ X : C, (a X).hom ≫ θ.app X = η.app X ≫ (b X).hom) (X : C) :
    ((arrowFunctorIso η θ a b ha hb hs).inv.app X).left = (a X).inv := rfl

/-- The target component of the inverse pointwise arrow isomorphism. -/
@[simp]
theorem arrowFunctorIso_inv_right
    {C D : Type*} [Category C] [Category D] {F G F' G' : C ⥤ D}
    (η : F ⟶ G) (θ : F' ⟶ G')
    (a : ∀ X : C, F.obj X ≅ F'.obj X) (b : ∀ X : C, G.obj X ≅ G'.obj X)
    (ha : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (a Y).hom = (a X).hom ≫ F'.map f)
    (hb : ∀ {X Y : C} (f : X ⟶ Y), G.map f ≫ (b Y).hom = (b X).hom ≫ G'.map f)
    (hs : ∀ X : C, (a X).hom ≫ θ.app X = η.app X ≫ (b X).hom) (X : C) :
    ((arrowFunctorIso η θ a b ha hb hs).inv.app X).right = (b X).inv := rfl

end NatTrans

end CategoryTheory
