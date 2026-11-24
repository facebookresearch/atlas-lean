/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductFunctor

/-! # Tests for left biproduct translation on the core -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.CategoryTheory.Limits.CoreBiproductFunctor

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasBinaryBiproducts C]

#check coreLeftBiprodFunctor
#check coreLeftBiprodFunctor_obj_of
#check coreLeftBiprodFunctor_map_iso_hom

example (A : C) : Core C ⥤ Core C :=
  coreLeftBiprodFunctor A

example (A : C) (X : Core C) :
    ((coreLeftBiprodFunctor A).obj X).of = (A ⊞ X.of : C) :=
  coreLeftBiprodFunctor_obj_of A X

example (A : C) {X Y : Core C} (g : X ⟶ Y) :
    ((coreLeftBiprodFunctor A).map g).iso.hom =
      biprod.map (𝟙 A) g.iso.hom :=
  coreLeftBiprodFunctor_map_iso_hom A g

/-- Boundary case: identity maps are handled by the inherited functor law. -/
example (A : C) (X : Core C) :
    (coreLeftBiprodFunctor A).map (𝟙 X) =
      𝟙 ((coreLeftBiprodFunctor A).obj X) :=
  (coreLeftBiprodFunctor A).map_id X

/-- The forward map formula at an identity simplifies to the identity of the
chosen biproduct. -/
example (A : C) (X : Core C) :
    (((coreLeftBiprodFunctor A).map (𝟙 X)).iso.hom) =
      𝟙 (A ⊞ X.of) := by
  simp

/-- Boundary case: a zero left summand remains the chosen biproduct with zero;
no literal identity-functor equality is asserted. -/
example [HasZeroObject C] (X : Core C) :
    ((coreLeftBiprodFunctor (0 : C)).obj X).of =
      ((0 : C) ⊞ X.of : C) :=
  coreLeftBiprodFunctor_obj_of (0 : C) X

example [HasZeroObject C] {X Y : Core C} (g : X ⟶ Y) :
    ((coreLeftBiprodFunctor (0 : C)).map g).iso.hom =
      biprod.map (𝟙 (0 : C)) g.iso.hom :=
  coreLeftBiprodFunctor_map_iso_hom (0 : C) g

#print axioms coreLeftBiprodFunctor
#print axioms coreLeftBiprodFunctor_obj_of
#print axioms coreLeftBiprodFunctor_map_iso_hom

end MathlibExtTest.CategoryTheory.Limits.CoreBiproductFunctor

end
