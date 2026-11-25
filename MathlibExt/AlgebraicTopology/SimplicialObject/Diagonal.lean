/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Diagonal and transpose of simplicial objects

This file defines the diagonal of a simplicial object in simplicial objects
in an arbitrary category. Constant objects and transposed diagonals have
canonical identity-component comparisons with their original objects.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Functor Opposite

universe v u

namespace CategoryTheory.SimplicialObject

variable (C : Type u) [Category.{v} C]

/-- The diagonal of a simplicial object in simplicial objects. -/
def diagonalFunctor :
    SimplicialObject (SimplicialObject C) ⥤ SimplicialObject C :=
  flipFunctor _ _ _ ⋙ Functor.uncurry ⋙
    (whiskeringLeft _ _ _).obj (Functor.diag SimplexCategoryᵒᵖ)

@[simp]
theorem diagonalFunctor_obj (X : SimplicialObject (SimplicialObject C))
    (a : SimplexCategoryᵒᵖ) :
    ((diagonalFunctor C).obj X).obj a = (X.obj a).obj a :=
  rfl

@[simp]
theorem diagonalFunctor_map_app
    {X Y : SimplicialObject (SimplicialObject C)} (f : X ⟶ Y)
    (a : SimplexCategoryᵒᵖ) :
    ((diagonalFunctor C).map f).app a = (f.app a).app a :=
  rfl

@[simp]
theorem diagonalFunctor_obj_map
    (X : SimplicialObject (SimplicialObject C))
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    ((diagonalFunctor C).obj X).map f =
      (X.obj a).map f ≫ (X.map f).app b :=
  rfl

/-- The diagonal of a constant outer simplicial object is the original
inner simplicial object, through the identity components. -/
def diagonalConstIso (Y : SimplicialObject C) :
    (diagonalFunctor C).obj ((const (SimplicialObject C)).obj Y) ≅ Y :=
  NatIso.ofComponents (fun a => Iso.refl (Y.obj a)) (by
    intro a b f
    change (Y.map f ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫ Y.map f
    simp only [Category.comp_id, Category.id_comp])

@[simp]
theorem diagonalConstIso_hom_app (Y : SimplicialObject C)
    (a : SimplexCategoryᵒᵖ) :
    (diagonalConstIso C Y).hom.app a = 𝟙 (Y.obj a) :=
  rfl

@[simp]
theorem diagonalConstIso_inv_app (Y : SimplicialObject C)
    (a : SimplexCategoryᵒᵖ) :
    (diagonalConstIso C Y).inv.app a = 𝟙 (Y.obj a) :=
  rfl

/-- The constant-diagonal comparison is natural in the original
inner simplicial object. -/
@[reassoc]
theorem diagonalConstIso_naturality
    {Y Z : SimplicialObject C} (f : Y ⟶ Z) :
    (diagonalFunctor C).map ((const (SimplicialObject C)).map f) ≫
        (diagonalConstIso C Z).hom =
      (diagonalConstIso C Y).hom ≫ f := by
  ext a
  change f.app a ≫ 𝟙 _ = 𝟙 _ ≫ f.app a
  simp only [Category.comp_id, Category.id_comp]

/-- Exchange the two simplicial variables. -/
def transposeFunctor :
    SimplicialObject (SimplicialObject C) ⥤
      SimplicialObject (SimplicialObject C) :=
  flipFunctor _ _ _

@[simp]
theorem transposeFunctor_obj_obj
    (X : SimplicialObject (SimplicialObject C))
    (a b : SimplexCategoryᵒᵖ) :
    (((transposeFunctor C).obj X).obj a).obj b =
      (X.obj b).obj a :=
  rfl

@[simp]
theorem transposeFunctor_map_app
    {X Y : SimplicialObject (SimplicialObject C)} (f : X ⟶ Y)
    (a b : SimplexCategoryᵒᵖ) :
    (((transposeFunctor C).map f).app a).app b =
      (f.app b).app a :=
  rfl

theorem diagonalTranspose_obj_map
    (X : SimplicialObject (SimplicialObject C))
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    ((diagonalFunctor C).obj ((transposeFunctor C).obj X)).map f =
      (X.map f).app a ≫ (X.obj b).map f :=
  rfl

/-- Transposition leaves the diagonal canonically unchanged. -/
def diagonalTransposeIso (X : SimplicialObject (SimplicialObject C)) :
    (diagonalFunctor C).obj ((transposeFunctor C).obj X) ≅
      (diagonalFunctor C).obj X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    change ((X.map f).app a ≫ (X.obj b).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ ((X.obj a).map f ≫ (X.map f).app b)
    simp only [Category.comp_id, Category.id_comp]
    exact ((X.map f).naturality f).symm)

@[simp]
theorem diagonalTransposeIso_hom_app
    (X : SimplicialObject (SimplicialObject C))
    (a : SimplexCategoryᵒᵖ) :
    (diagonalTransposeIso C X).hom.app a = 𝟙 _ :=
  rfl

@[simp]
theorem diagonalTransposeIso_inv_app
    (X : SimplicialObject (SimplicialObject C))
    (a : SimplexCategoryᵒᵖ) :
    (diagonalTransposeIso C X).inv.app a = 𝟙 _ :=
  rfl

@[reassoc]
theorem diagonalTransposeIso_naturality
    {X Y : SimplicialObject (SimplicialObject C)} (f : X ⟶ Y) :
    (diagonalFunctor C).map ((transposeFunctor C).map f) ≫
        (diagonalTransposeIso C Y).hom =
      (diagonalTransposeIso C X).hom ≫ (diagonalFunctor C).map f := by
  ext a
  simp

end CategoryTheory.SimplicialObject
