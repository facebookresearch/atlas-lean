/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductMultiplication

/-! # Tests for core left-biproduct multiplication coherence -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.CategoryTheory.Limits.CoreBiproductMultiplication

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check coreLeftBiprodIsoOfIso
#check coreLeftBiprodIsoOfIso_hom_app_iso_hom
#check coreLeftBiprodBiprodIso
#check coreLeftBiprodBiprodIso_hom_app_iso_hom

example {A B : C} (e : A ≅ B) :
    coreLeftBiprodFunctor A ≅ coreLeftBiprodFunctor B :=
  coreLeftBiprodIsoOfIso e

example (A B : C) :
    coreLeftBiprodFunctor (A ⊞ B) ≅
      coreLeftBiprodFunctor B ⋙ coreLeftBiprodFunctor A :=
  coreLeftBiprodBiprodIso A B

example (A B : C) (X : Core C) :
    ((coreLeftBiprodBiprodIso A B).hom.app X).iso.hom =
      (biprod.associator A B X.of).hom :=
  coreLeftBiprodBiprodIso_hom_app_iso_hom A B X

/-- Boundary case: identity parameter isomorphism acts by the identity
biproduct map on each component. -/
example (A : C) (X : Core C) :
    ((coreLeftBiprodIsoOfIso (Iso.refl A)).hom.app X).iso.hom =
      𝟙 (A ⊞ X.of) := by
  rw [coreLeftBiprodIsoOfIso_hom_app_iso_hom]
  apply biprod.hom_ext <;> simp

/-- Boundary case: the multiplication component with zero in the first
parameter retains the forward associator orientation. -/
example (B : C) (X : Core C) :
    ((coreLeftBiprodBiprodIso (0 : C) B).hom.app X).iso.hom =
      (biprod.associator (0 : C) B X.of).hom :=
  coreLeftBiprodBiprodIso_hom_app_iso_hom (0 : C) B X

/-- Boundary case: likewise when the second parameter is zero. -/
example (A : C) (X : Core C) :
    ((coreLeftBiprodBiprodIso A (0 : C)).hom.app X).iso.hom =
      (biprod.associator A (0 : C) X.of).hom :=
  coreLeftBiprodBiprodIso_hom_app_iso_hom A (0 : C) X

/-- Boundary case: naturality of multiplication at an identity core map. -/
example (A B : C) (X : Core C) :
    (coreLeftBiprodFunctor (A ⊞ B)).map (𝟙 X) ≫
        (coreLeftBiprodBiprodIso A B).hom.app X =
      (coreLeftBiprodBiprodIso A B).hom.app X ≫
        (coreLeftBiprodFunctor B ⋙
          coreLeftBiprodFunctor A).map (𝟙 X) :=
  (coreLeftBiprodBiprodIso A B).hom.naturality (𝟙 X)

#print axioms coreLeftBiprodIsoOfIso
#print axioms coreLeftBiprodIsoOfIso_hom_app_iso_hom
#print axioms coreLeftBiprodBiprodIso
#print axioms coreLeftBiprodBiprodIso_hom_app_iso_hom

end MathlibExtTest.CategoryTheory.Limits.CoreBiproductMultiplication

end
