/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Canonical bare biproduct functor

The functor `C × C ⥤ C` sending `(X, Y)` to the chosen binary biproduct
`X ⊞ Y`, with maps built from the pinned `biprod.map`.

This is a minimal wrapper around the pinned Mathlib `HasBinaryBiproducts` /
`biprod.map` APIs; no competing biproduct construction, new class, or custom
universal-property layer is introduced. Object/map behavior and the
projection/inclusion computation laws reuse `biprod.map_fst`, `biprod.map_snd`,
`biprod.inl_map`, `biprod.inr_map`, and biproduct extensionality.

Nonclaims: no `Functor.Additive` or `Functor.IsExact` instance is stated here;
product preadditive/exact instances are a separate gate. No Waldhausen or
additivity theorem, simplicial object, realization, K/G-theory identification,
spectrum, or Q/S comparison is claimed.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Limits

universe v u

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

noncomputable section

/-- Canonical bare biproduct functor: `(X, Y) ↦ X ⊞ Y` via `biprod.map`. -/
noncomputable def biprodFunctor : C × C ⥤ C where
  obj X := X.1 ⊞ X.2
  map f := biprod.map f.1 f.2
  map_id X := by
    apply biprod.hom_ext'
    · simp
    · simp
  map_comp f g := by
    apply biprod.hom_ext'
    · simp [Category.assoc]
    · simp [Category.assoc]

@[simp]
theorem biprodFunctor_obj (X : C × C) :
    (biprodFunctor C).obj X = (X.1 ⊞ X.2) :=
  rfl

@[simp]
theorem biprodFunctor_map {X Y : C × C} (f : X ⟶ Y) :
    (biprodFunctor C).map f = biprod.map f.1 f.2 :=
  rfl

@[reassoc (attr := simp)]
theorem biprodFunctor_map_fst {X Y : C × C} (f : X ⟶ Y) :
    (biprodFunctor C).map f ≫ biprod.fst = biprod.fst ≫ f.1 :=
  biprod.map_fst _ _

@[reassoc (attr := simp)]
theorem biprodFunctor_map_snd {X Y : C × C} (f : X ⟶ Y) :
    (biprodFunctor C).map f ≫ biprod.snd = biprod.snd ≫ f.2 :=
  biprod.map_snd _ _

@[reassoc (attr := simp)]
theorem biprodFunctor_inl_map {X Y : C × C} (f : X ⟶ Y) :
    biprod.inl ≫ (biprodFunctor C).map f = f.1 ≫ biprod.inl :=
  biprod.inl_map _ _

@[reassoc (attr := simp)]
theorem biprodFunctor_inr_map {X Y : C × C} (f : X ⟶ Y) :
    biprod.inr ≫ (biprodFunctor C).map f = f.2 ≫ biprod.inr :=
  biprod.inr_map _ _

end

end CategoryTheory.Limits
