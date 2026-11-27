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
public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductLeftTriangle

/-! # Tests for the zero-first-parameter core biproduct triangle -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.CategoryTheory.Limits.CoreBiproductLeftTriangle

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check coreLeftBiprodBiprodIso_leftUnit_component
#check coreLeftBiprodBiprodIso_leftUnit

example (B : C) :
    coreLeftBiprodBiprodIso (0 : C) B ≪≫
        Functor.isoWhiskerLeft (coreLeftBiprodFunctor B)
          coreLeftBiprodZeroIso ≪≫
        Functor.rightUnitor (coreLeftBiprodFunctor B) =
      coreLeftBiprodIsoOfIso
        (isoZeroBiprod (isZero_zero C)).symm :=
  coreLeftBiprodBiprodIso_leftUnit B

/-- Boundary case: the second parameter is also zero. -/
example :
    coreLeftBiprodBiprodIso (0 : C) (0 : C) ≪≫
        Functor.isoWhiskerLeft (coreLeftBiprodFunctor (0 : C))
          coreLeftBiprodZeroIso ≪≫
        Functor.rightUnitor (coreLeftBiprodFunctor (0 : C)) =
      coreLeftBiprodIsoOfIso
        (isoZeroBiprod (isZero_zero C)).symm :=
  coreLeftBiprodBiprodIso_leftUnit (0 : C)

/-- Boundary case: naturality of the multiplication component at an identity
core morphism. -/
example (B : C) (X : Core C) :
    (coreLeftBiprodFunctor ((0 : C) ⊞ B)).map (𝟙 X) ≫
        (coreLeftBiprodBiprodIso (0 : C) B).hom.app X =
      (coreLeftBiprodBiprodIso (0 : C) B).hom.app X ≫
        (coreLeftBiprodFunctor B ⋙
          coreLeftBiprodFunctor (0 : C)).map (𝟙 X) :=
  (coreLeftBiprodBiprodIso (0 : C) B).hom.naturality (𝟙 X)

/-- Boundary case: the companion triangle is available in a zero category. -/
example :
    coreLeftBiprodBiprodIso
          (0 : ModuleCat (ZMod 1)) (0 : ModuleCat (ZMod 1)) ≪≫
        Functor.isoWhiskerLeft
          (coreLeftBiprodFunctor (0 : ModuleCat (ZMod 1)))
          coreLeftBiprodZeroIso ≪≫
        Functor.rightUnitor
          (coreLeftBiprodFunctor (0 : ModuleCat (ZMod 1))) =
      coreLeftBiprodIsoOfIso
        (isoZeroBiprod (isZero_zero (ModuleCat (ZMod 1)))).symm :=
  coreLeftBiprodBiprodIso_leftUnit (0 : ModuleCat (ZMod 1))

#print axioms coreLeftBiprodBiprodIso_leftUnit_component
#print axioms coreLeftBiprodBiprodIso_leftUnit

end MathlibExtTest.CategoryTheory.Limits.CoreBiproductLeftTriangle

end
