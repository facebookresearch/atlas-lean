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
public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductTriangle

/-! # Tests for the right-unit triangle of core biproduct translation -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.CategoryTheory.Limits.CoreBiproductTriangle

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check coreLeftBiprodBiprodIso_rightUnit_component
#check coreLeftBiprodBiprodIso_rightUnit

example (A : C) :
    coreLeftBiprodBiprodIso A (0 : C) ≪≫
        Functor.isoWhiskerRight coreLeftBiprodZeroIso
          (coreLeftBiprodFunctor A) ≪≫
        Functor.leftUnitor (coreLeftBiprodFunctor A) =
      coreLeftBiprodIsoOfIso
        (isoBiprodZero (isZero_zero C)).symm :=
  coreLeftBiprodBiprodIso_rightUnit A

/-- Boundary case: the translating parameter itself is zero. -/
example :
    coreLeftBiprodBiprodIso (0 : C) (0 : C) ≪≫
        Functor.isoWhiskerRight coreLeftBiprodZeroIso
          (coreLeftBiprodFunctor (0 : C)) ≪≫
        Functor.leftUnitor (coreLeftBiprodFunctor (0 : C)) =
      coreLeftBiprodIsoOfIso
        (isoBiprodZero (isZero_zero C)).symm :=
  coreLeftBiprodBiprodIso_rightUnit (0 : C)

/-- Boundary case: the component at the core object represented by zero. -/
example (A : C) :
    (biprod.associator A (0 : C) (0 : C)).hom ≫
        biprod.map (𝟙 A)
          (isoZeroBiprod (isZero_zero C)).symm.hom =
      biprod.map (isoBiprodZero (isZero_zero C)).symm.hom
        (𝟙 (0 : C)) :=
  coreLeftBiprodBiprodIso_rightUnit_component A (0 : C)

/-- Boundary case: naturality of the triangle's multiplication component at
an identity core morphism. -/
example (A : C) (X : Core C) :
    (coreLeftBiprodFunctor (A ⊞ (0 : C))).map (𝟙 X) ≫
        (coreLeftBiprodBiprodIso A (0 : C)).hom.app X =
      (coreLeftBiprodBiprodIso A (0 : C)).hom.app X ≫
        (coreLeftBiprodFunctor (0 : C) ⋙
          coreLeftBiprodFunctor A).map (𝟙 X) :=
  (coreLeftBiprodBiprodIso A (0 : C)).hom.naturality (𝟙 X)

/-- Boundary case: the triangle is available in a zero category. -/
example :
    coreLeftBiprodBiprodIso (0 : ModuleCat (ZMod 1)) 0 ≪≫
        Functor.isoWhiskerRight coreLeftBiprodZeroIso
          (coreLeftBiprodFunctor (0 : ModuleCat (ZMod 1))) ≪≫
        Functor.leftUnitor
          (coreLeftBiprodFunctor (0 : ModuleCat (ZMod 1))) =
      coreLeftBiprodIsoOfIso
        (isoBiprodZero (isZero_zero (ModuleCat (ZMod 1)))).symm :=
  coreLeftBiprodBiprodIso_rightUnit (0 : ModuleCat (ZMod 1))

#print axioms coreLeftBiprodBiprodIso_rightUnit_component
#print axioms coreLeftBiprodBiprodIso_rightUnit

end MathlibExtTest.CategoryTheory.Limits.CoreBiproductTriangle

end
