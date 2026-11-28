/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Arrows as one-step composable diagrams

For a category C, an object of Arrow C is a morphism A.left → A.right, and a morphism of
arrows is a commuting square. A one-step composable diagram consists of the same two objects
and one morphism, with natural transformations given by the two sides of such squares.

The functors in both directions retain the source, target, arrow and square components. The
displayed component formulas identify an arrow square with the natural transformation on its
two vertices. The object and morphism universes of C are independent.
-/

@[expose] public section

namespace CategoryTheory

namespace ComposableArrows

universe v u

variable {C : Type u} [Category.{v} C]

/-- Functor from arrows to one-step diagrams.

For a category C, send an arrow A to the diagram A.left → A.right with edge A.hom. A commuting
square f : A ⟶ B is sent to the natural transformation with components f.left and f.right at
vertices 0 and 1. -/
def ofArrowFunctor : Arrow C ⥤ ComposableArrows C 1 where
  obj A := mk₁ A.hom
  map f := homMk₁ f.left f.right (Arrow.w f).symm
  map_id A := by apply hom_ext₁ <;> rfl
  map_comp f g := by apply hom_ext₁ <;> rfl

/-- Source vertex of the diagram associated to an arrow.

For an arrow A in a category C, the left vertex of ofArrowFunctor(A) is A.left. -/
@[simp]
lemma ofArrowFunctor_obj_left (A : Arrow C) : (ofArrowFunctor.obj A).left = A.left := rfl

/-- Target vertex of the diagram associated to an arrow.

For an arrow A in a category C, the right vertex of ofArrowFunctor(A) is A.right. -/
@[simp]
lemma ofArrowFunctor_obj_right (A : Arrow C) : (ofArrowFunctor.obj A).right = A.right := rfl

/-- Edge of the diagram associated to an arrow.

For an arrow A in a category C, the morphism of the one-step diagram ofArrowFunctor(A) is
A.hom : A.left → A.right. -/
@[simp]
lemma ofArrowFunctor_obj_hom (A : Arrow C) : (ofArrowFunctor.obj A).hom = A.hom := rfl

/-- Source component of an arrow square as a diagram map.

For a commuting square f : A ⟶ B in Arrow C, the component at vertex 0 of
ofArrowFunctor.map(f) is the left side f.left : A.left → B.left. -/
@[simp]
lemma ofArrowFunctor_map_app_zero {A B : Arrow C} (f : A ⟶ B) :
    (ofArrowFunctor.map f).app 0 = f.left := rfl

/-- Target component of an arrow square as a diagram map.

For a commuting square f : A ⟶ B in Arrow C, the component at vertex 1 of
ofArrowFunctor.map(f) is the right side f.right : A.right → B.right. -/
@[simp]
lemma ofArrowFunctor_map_app_one {A B : Arrow C} (f : A ⟶ B) :
    (ofArrowFunctor.map f).app 1 = f.right := rfl

/-- Diagram map determined by a commuting arrow square.

Let left : A.left → B.left and right : A.right → B.right satisfy left ≫ B.hom = A.hom ≫ right.
Applying ofArrowFunctor to this arrow square gives homMk₁(left,right,w.symm), the natural
transformation with these two components; its naturality equation uses the symmetric form of
the square equation. -/
lemma ofArrowFunctor_map_homMk {A B : Arrow C}
    (left : A.left ⟶ B.left) (right : A.right ⟶ B.right)
    (w : left ≫ B.hom = A.hom ≫ right) :
    ofArrowFunctor.map (Arrow.homMk left right w) = homMk₁ left right w.symm := rfl

/-- Functor from one-step diagrams to arrows.

For a category C, send a diagram F in ComposableArrows C 1 to its edge F.left → F.right. A
natural transformation φ : F ⟶ G becomes the commuting arrow square with left component φ₀ and
right component φ₁. -/
def arrowFunctor : ComposableArrows C 1 ⥤ Arrow C where
  obj := arrowEquiv
  map {X Y} f := Arrow.homMk (app' f 0) (app' f 1) ((naturality' f 0 1).symm)

/-- Source of the arrow associated to a one-step diagram.

For F in ComposableArrows C 1, the source of arrowFunctor(F) is the left vertex F.left. -/
@[simp]
lemma arrowFunctor_obj_left (F : ComposableArrows C 1) :
    (arrowFunctor (C := C).obj F).left = F.left :=
  rfl

/-- Target of the arrow associated to a one-step diagram.

For F in ComposableArrows C 1, the target of arrowFunctor(F) is the right vertex F.right. -/
@[simp]
lemma arrowFunctor_obj_right (F : ComposableArrows C 1) :
    (arrowFunctor (C := C).obj F).right = F.right :=
  rfl

/-- Morphism of the arrow associated to a one-step diagram.

For F in ComposableArrows C 1, the morphism of arrowFunctor(F) is its edge F.hom : F.left →
F.right. -/
@[simp]
lemma arrowFunctor_obj_hom (F : ComposableArrows C 1) :
    (arrowFunctor (C := C).obj F).hom = F.hom :=
  rfl

/-- Left side of the arrow square associated to a diagram map.

For a natural transformation φ : F ⟶ G between one-step diagrams, the left component of
arrowFunctor.map(φ) is app' φ 0, the map on the source vertex. -/
@[simp]
lemma arrowFunctor_map_left {F G : ComposableArrows C 1} (φ : F ⟶ G) :
    (arrowFunctor (C := C).map φ).left = app' φ 0 :=
  rfl

/-- Right side of the arrow square associated to a diagram map.

For a natural transformation φ : F ⟶ G between one-step diagrams, the right component of
arrowFunctor.map(φ) is app' φ 1, the map on the target vertex. -/
@[simp]
lemma arrowFunctor_map_right {F G : ComposableArrows C 1} (φ : F ⟶ G) :
    (arrowFunctor (C := C).map φ).right = app' φ 1 :=
  rfl

end ComposableArrows

end CategoryTheory
