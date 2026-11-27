/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Data.ZMod.Basic
public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductPentagon

/-! # Tests for the core biproduct translation pentagon -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.CategoryTheory.Limits.CoreBiproductPentagon

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

private abbrev ZeroModuleCat := ModuleCat (ZMod 1)

#check coreLeftBiprodBiprodIso_pentagon_component
#check coreLeftBiprodBiprodIso_pentagon

example (A B D : C) :
    coreLeftBiprodBiprodIso (A ⊞ B) D ≪≫
        Functor.isoWhiskerLeft (coreLeftBiprodFunctor D)
          (coreLeftBiprodBiprodIso A B) =
      coreLeftBiprodIsoOfIso (biprod.associator A B D) ≪≫
        coreLeftBiprodBiprodIso A (B ⊞ D) ≪≫
        Functor.isoWhiskerRight (coreLeftBiprodBiprodIso B D)
          (coreLeftBiprodFunctor A) ≪≫
        Functor.associator (coreLeftBiprodFunctor D)
          (coreLeftBiprodFunctor B) (coreLeftBiprodFunctor A) :=
  coreLeftBiprodBiprodIso_pentagon A B D

/-- Boundary case: all three parameters are zero. -/
example :
    coreLeftBiprodBiprodIso ((0 : C) ⊞ (0 : C)) (0 : C) ≪≫
        Functor.isoWhiskerLeft (coreLeftBiprodFunctor (0 : C))
          (coreLeftBiprodBiprodIso (0 : C) (0 : C)) =
      coreLeftBiprodIsoOfIso
          (biprod.associator (0 : C) (0 : C) (0 : C)) ≪≫
        coreLeftBiprodBiprodIso (0 : C) ((0 : C) ⊞ (0 : C)) ≪≫
        Functor.isoWhiskerRight
          (coreLeftBiprodBiprodIso (0 : C) (0 : C))
          (coreLeftBiprodFunctor (0 : C)) ≪≫
        Functor.associator (coreLeftBiprodFunctor (0 : C))
          (coreLeftBiprodFunctor (0 : C))
          (coreLeftBiprodFunctor (0 : C)) :=
  coreLeftBiprodBiprodIso_pentagon (0 : C) (0 : C) (0 : C)

/-- Boundary case: naturality of one pentagon route at an identity core
morphism. -/
example (A B D : C) (X : Core C) :
    let p := coreLeftBiprodBiprodIso (A ⊞ B) D ≪≫
      Functor.isoWhiskerLeft (coreLeftBiprodFunctor D)
        (coreLeftBiprodBiprodIso A B)
    (coreLeftBiprodFunctor ((A ⊞ B) ⊞ D)).map (𝟙 X) ≫
        p.hom.app X =
      p.hom.app X ≫
        (coreLeftBiprodFunctor D ⋙
          (coreLeftBiprodFunctor B ⋙
            coreLeftBiprodFunctor A)).map (𝟙 X) := by
  dsimp only
  exact
    (coreLeftBiprodBiprodIso (A ⊞ B) D ≪≫
      Functor.isoWhiskerLeft (coreLeftBiprodFunctor D)
        (coreLeftBiprodBiprodIso A B)).hom.naturality (𝟙 X)

/-- Boundary case: the pentagon is available in a zero category. -/
example :
    (biprod.associator
          ((0 : ZeroModuleCat) ⊞ 0) 0 0).hom ≫
        (biprod.associator
          (0 : ZeroModuleCat) 0 ((0 : ZeroModuleCat) ⊞ 0)).hom =
      biprod.map
          (biprod.associator
            (0 : ZeroModuleCat) 0 0).hom (𝟙 (0 : ZeroModuleCat)) ≫
        (biprod.associator
          (0 : ZeroModuleCat) ((0 : ZeroModuleCat) ⊞ 0) 0).hom ≫
        biprod.map (𝟙 (0 : ZeroModuleCat))
          (biprod.associator
            (0 : ZeroModuleCat) 0 0).hom :=
  coreLeftBiprodBiprodIso_pentagon_component
    (0 : ZeroModuleCat) 0 0 0

#print axioms coreLeftBiprodBiprodIso_pentagon_component
#print axioms coreLeftBiprodBiprodIso_pentagon

end MathlibExtTest.CategoryTheory.Limits.CoreBiproductPentagon

end
