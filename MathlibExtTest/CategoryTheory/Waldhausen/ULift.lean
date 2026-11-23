/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.ULift
public import Batteries.Tactic.Lint

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open scoped ZeroObject

namespace WaldhausenULiftTests

universe u v

attribute [local instance] CategoryTheory.uliftCategory

section Generic

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategory C]

local instance : HasZeroObject (ULift.{v} C) := uliftHasZeroObject.{u, v} C
local instance : WaldhausenCategory (ULift.{v} C) := uliftWaldhausenCategory.{u, v} C

example (X Y : ULift.{v} C) :
    (X ⟶ Y) = (X.down ⟶ Y.down) := rfl

example {X Y : C} (f : X ⟶ Y) :
    (ULift.upFunctor : C ⥤ ULift.{v} C).map f = f := rfl

example :
    (ULift.upFunctor : C ⥤ ULift.{v} C).obj (0 : C) = uliftZeroObject.{u, v} C :=
  uliftZeroObject_up.{u, v} C

example :
    (ULift.downFunctor : ULift.{v} C ⥤ C).obj (uliftZeroObject.{u, v} C) = (0 : C) :=
  uliftZeroObject_down.{u, v} C

example :
    (uliftChosenZeroDownIso.{u, v} C).hom = (isZero_zero C).from_ ((0 : ULift.{v} C).down) :=
  uliftChosenZeroDownIso_hom.{u, v} C

example {X Y : C} (f : X ⟶ Y) :
    IsCofibration ((ULift.upFunctor : C ⥤ ULift.{v} C).map f) ↔ IsCofibration f :=
  uliftUp_isCofibration_iff.{u, v} C f

example {X Y : ULift.{v} C} (f : X ⟶ Y) :
    IsWeakEquivalence f ↔ IsWeakEquivalence ((ULift.downFunctor : ULift.{v} C ⥤ C).map f) :=
  ulift_isWeakEquivalence_iff.{u, v} C f

example :
    (show C ≌ ULift.{v} C from ULift.equivalence).functor.IsWaldhausenExact ∧
      (show C ≌ ULift.{v} C from ULift.equivalence).inverse.IsWaldhausenExact :=
  uliftEquivalence_isWaldhausenExact.{u, v} C

example {X Y Z P : ULift.{v} C}
    (f : X ⟶ Y) (i : X ⟶ Z) (l : Y ⟶ P) (r : Z ⟶ P) :
    IsPushout f i l r ↔ IsPushout
      ((ULift.downFunctor : ULift.{v} C ⥤ C).map f)
      ((ULift.downFunctor : ULift.{v} C ⥤ C).map i)
      ((ULift.downFunctor : ULift.{v} C ⥤ C).map l)
      ((ULift.downFunctor : ULift.{v} C ⥤ C).map r) :=
  ulift_isPushout_iff.{u, v} C f i l r

example :
    WaldhausenGluingAxiom (C := ULift.{v} C) ↔ WaldhausenGluingAxiom (C := C) :=
  uliftGluing_iff.{u, v} C

end Generic

section HigherHomWorld

variable (C : Type) [Category.{1} C] [HasZeroObject C] [WaldhausenCategory C]

local instance : HasZeroObject (ULift.{1} C) := uliftHasZeroObject.{0, 1} C
local instance : WaldhausenCategory (ULift.{1} C) := uliftWaldhausenCategory.{0, 1} C

example : (ULift.downFunctor : ULift.{1} C ⥤ C).IsWaldhausenExact :=
  uliftDown_isWaldhausenExact.{0, 1} C

example (X Y : ULift.{1} C) :
    (X ⟶ Y) = (X.down ⟶ Y.down) := rfl

end HigherHomWorld

#print axioms CategoryTheory.Waldhausen.ulift_isZero_iff
#print axioms CategoryTheory.Waldhausen.ulift_isPushout_iff
#print axioms CategoryTheory.Waldhausen.uliftZeroObject
#print axioms CategoryTheory.Waldhausen.uliftZeroObject_isZero
#print axioms CategoryTheory.Waldhausen.uliftZeroObject_up
#print axioms CategoryTheory.Waldhausen.uliftZeroObject_down
#print axioms CategoryTheory.Waldhausen.uliftHasZeroObject
#print axioms CategoryTheory.Waldhausen.uliftZeroObjectIsoZero
#print axioms CategoryTheory.Waldhausen.uliftChosenZero_down_isZero
#print axioms CategoryTheory.Waldhausen.uliftChosenZeroDownIso
#print axioms CategoryTheory.Waldhausen.uliftZeroObjectIsoZero_hom
#print axioms CategoryTheory.Waldhausen.uliftZeroObjectIsoZero_inv
#print axioms CategoryTheory.Waldhausen.uliftChosenZeroDownIso_hom
#print axioms CategoryTheory.Waldhausen.uliftChosenZeroDownIso_inv
#print axioms CategoryTheory.Waldhausen.uliftWaldhausenCategory
#print axioms CategoryTheory.Waldhausen.ulift_isCofibration_iff
#print axioms CategoryTheory.Waldhausen.ulift_isWeakEquivalence_iff
#print axioms CategoryTheory.Waldhausen.uliftUp_isCofibration_iff
#print axioms CategoryTheory.Waldhausen.uliftUp_isWeakEquivalence_iff
#print axioms CategoryTheory.Waldhausen.uliftDown_isWaldhausenExact
#print axioms CategoryTheory.Waldhausen.uliftUp_isWaldhausenExact
#print axioms CategoryTheory.Waldhausen.uliftEquivalence_isWaldhausenExact
#print axioms CategoryTheory.Waldhausen.uliftGluing
#print axioms CategoryTheory.Waldhausen.uliftGluing_iff

#lint only unusedArguments in MathlibExt.CategoryTheory.Waldhausen.ULift

end WaldhausenULiftTests
