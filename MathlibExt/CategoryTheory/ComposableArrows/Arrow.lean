/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

@[expose] public section

namespace CategoryTheory

namespace ComposableArrows

universe v u

variable {C : Type u} [Category.{v} C]

/-- The full Arrow square gives its two-object diagram and natural transformation. -/
def ofArrowFunctor : Arrow C ⥤ ComposableArrows C 1 where
  obj A := mk₁ A.hom
  map f := homMk₁ f.left f.right (Arrow.w f).symm
  map_id A := by apply hom_ext₁ <;> rfl
  map_comp f g := by apply hom_ext₁ <;> rfl

/-- The two-object diagram retains the original source object. -/
@[simp]
lemma ofArrowFunctor_obj_left (A : Arrow C) : (ofArrowFunctor.obj A).left = A.left := rfl

/-- The two-object diagram retains the original target object. -/
@[simp]
lemma ofArrowFunctor_obj_right (A : Arrow C) : (ofArrowFunctor.obj A).right = A.right := rfl

/-- The diagram retains the original arrow morphism. -/
@[simp]
lemma ofArrowFunctor_obj_hom (A : Arrow C) : (ofArrowFunctor.obj A).hom = A.hom := rfl

/-- The natural transformation retains the original square source component. -/
@[simp]
lemma ofArrowFunctor_map_app_zero {A B : Arrow C} (f : A ⟶ B) :
    (ofArrowFunctor.map f).app 0 = f.left := rfl

/-- The natural transformation retains the original square target component. -/
@[simp]
lemma ofArrowFunctor_map_app_one {A B : Arrow C} (f : A ⟶ B) :
    (ofArrowFunctor.map f).app 1 = f.right := rfl

/-- Every given square retains its original commutativity proof in the required naturality direction. -/
lemma ofArrowFunctor_map_homMk {A B : Arrow C}
    (left : A.left ⟶ B.left) (right : A.right ⟶ B.right)
    (w : left ≫ B.hom = A.hom ≫ right) :
    ofArrowFunctor.map (Arrow.homMk left right w) = homMk₁ left right w.symm := rfl

/-- Functor from `ComposableArrows C 1` to `Arrow C` whose object map is `arrowEquiv`. -/
def arrowFunctor : ComposableArrows C 1 ⥤ Arrow C where
  obj := arrowEquiv
  map {X Y} f := Arrow.homMk (app' f 0) (app' f 1) ((naturality' f 0 1).symm)

@[simp]
lemma arrowFunctor_obj_left (F : ComposableArrows C 1) :
    (arrowFunctor (C := C).obj F).left = F.left :=
  rfl

@[simp]
lemma arrowFunctor_obj_right (F : ComposableArrows C 1) :
    (arrowFunctor (C := C).obj F).right = F.right :=
  rfl

@[simp]
lemma arrowFunctor_obj_hom (F : ComposableArrows C 1) :
    (arrowFunctor (C := C).obj F).hom = F.hom :=
  rfl

@[simp]
lemma arrowFunctor_map_left {F G : ComposableArrows C 1} (φ : F ⟶ G) :
    (arrowFunctor (C := C).map φ).left = app' φ 0 :=
  rfl

@[simp]
lemma arrowFunctor_map_right {F G : ComposableArrows C 1} (φ : F ⟶ G) :
    (arrowFunctor (C := C).map φ).right = app' φ 1 :=
  rfl

end ComposableArrows

end CategoryTheory
