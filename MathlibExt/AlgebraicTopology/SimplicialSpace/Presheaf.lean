/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# The presheaf presentation of designated simplicial spaces

The designated simplicial-space category is canonically equivalent to
`Type`-valued presheaves on the product simplex category. The first product
coordinate is the outer simplicial-space degree and the second is the inner
simplicial-set degree.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace SimplicialSpace

/-- The canonical outer-first, inner-second presheaf presentation of the
designated simplicial-space category. -/
def equivalencePresheaf :
    SimplicialSpace.{u} ≌ ((SimplexCategory × SimplexCategory)ᵒᵖ ⥤ Type u) :=
  equivalenceSimplicialObject.trans
    (Functor.currying.trans
      ((prodOpEquiv (C := SimplexCategory) (D := SimplexCategory)).symm.congrLeft))

/-- Forget the designation and uncurry the two simplicial directions, with the
outer degree first and the inner degree second. -/
abbrev toPresheaf :
    SimplicialSpace.{u} ⥤ ((SimplexCategory × SimplexCategory)ᵒᵖ ⥤ Type u) :=
  equivalencePresheaf.functor

instance : toPresheaf.{u}.IsEquivalence :=
  equivalencePresheaf.isEquivalence_functor

@[simp]
theorem toPresheaf_obj_obj (X : SimplicialSpace.{u})
    (p : (SimplexCategory × SimplexCategory)ᵒᵖ) :
    (toPresheaf.obj X).obj p =
      (X.diagram.obj (op p.unop.1)).obj (op p.unop.2) :=
  rfl

@[simp]
theorem toPresheaf_map_app {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (p : (SimplexCategory × SimplexCategory)ᵒᵖ) :
    (toPresheaf.map f).app p =
      (f.hom.app (op p.unop.1)).app (op p.unop.2) :=
  rfl

/-- Original outer-then-inner total points identify with the elements of the
canonical product-site presheaf. -/
def totalPointsEquivToPresheaf (X : SimplicialSpace.{u}) :
    (Functor.uncurry.obj X.diagram).Elements ≃
      (toPresheaf.obj X).Elements where
  toFun q := Functor.elementsMk _ (op (q.obj.1.unop, q.obj.2.unop)) q.val
  invFun q := Functor.elementsMk _ (op q.obj.unop.1, op q.obj.unop.2) q.val
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

/-- The total-point equivalence commutes with every original simplicial-space
map, retaining the outer and inner degrees. -/
theorem totalPointsEquivToPresheaf_map {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) (q : (Functor.uncurry.obj X.diagram).Elements) :
    totalPointsEquivToPresheaf Y
        ((Functor.uncurry.map f.hom).mapElements.obj q) =
      (toPresheaf.map f).mapElements.obj (totalPointsEquivToPresheaf X q) := by
  cases q
  rfl

end SimplicialSpace
