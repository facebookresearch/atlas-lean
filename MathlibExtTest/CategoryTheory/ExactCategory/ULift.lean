/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ExactCategory.ULift
public import Batteries.Tactic.Lint

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

namespace ExactCategoryULiftTests

universe u v

attribute [local instance] CategoryTheory.uliftCategory

section Generic

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]

local instance : Preadditive (ULift.{v} C) := uliftPreadditive.{u, v} C
local instance : HasZeroObject (ULift.{v} C) := Waldhausen.uliftHasZeroObject.{u, v} C
local instance : HasBinaryBiproducts (ULift.{v} C) := uliftHasBinaryBiproducts.{u, v} C
local instance : ExactCategory (ULift.{v} C) := uliftExactCategory.{u, v} C
local instance : (ULift.upFunctor : C ⥤ ULift.{v} C).Additive := uliftUp_additive.{u, v} C
local instance : (ULift.downFunctor : ULift.{v} C ⥤ C).Additive := uliftDown_additive.{u, v} C

example (X Y : ULift.{v} C) : (X ⟶ Y) = (X.down ⟶ Y.down) := rfl

example {X Y : C} (f g : X ⟶ Y) :
    (ULift.upFunctor : C ⥤ ULift.{v} C).map (f + g) = f + g := rfl

example (S : ShortComplex C) :
    (S.map (ULift.upFunctor : C ⥤ ULift.{v} C)).map
      (ULift.downFunctor : ULift.{v} C ⥤ C) = S :=
  uliftUp_down_mapShortComplex.{u, v} C S

example (S : ShortComplex (ULift.{v} C)) :
    S.ShortExact ↔ (S.map (ULift.downFunctor : ULift.{v} C ⥤ C)).ShortExact :=
  ulift_shortExact_iff.{u, v} C S

example (S : ShortComplex (ULift.{v} C)) :
    IsAdmissibleExact S ↔ IsAdmissibleExact (S.map (ULift.downFunctor : ULift.{v} C ⥤ C)) :=
  ulift_isAdmissibleExact_iff.{u, v} C S

example {X Y : ULift.{v} C} (f : X ⟶ Y) :
    IsAdmissibleMono f ↔ IsAdmissibleMono ((ULift.downFunctor : ULift.{v} C ⥤ C).map f) :=
  ulift_isAdmissibleMono_iff.{u, v} C f

example {X Y : ULift.{v} C} (f : X ⟶ Y) :
    IsAdmissibleEpi f ↔ IsAdmissibleEpi ((ULift.downFunctor : ULift.{v} C ⥤ C).map f) :=
  ulift_isAdmissibleEpi_iff.{u, v} C f

example (S : ShortComplex C) :
    IsAdmissibleExact (S.map (ULift.upFunctor : C ⥤ ULift.{v} C)) ↔ IsAdmissibleExact S :=
  uliftUp_isAdmissibleExact_iff.{u, v} C S

example : (ULift.downFunctor : ULift.{v} C ⥤ C).IsExact := uliftDown_isExact.{u, v} C

example : (ULift.upFunctor : C ⥤ ULift.{v} C).IsExact := uliftUp_isExact.{u, v} C

example (S : ShortComplex (ULift.{v} C))
    (s : (S.map (ULift.downFunctor : ULift.{v} C ⥤ C)).Splitting) :
    (uliftSplittingOfDown.{u, v} C S s).r = s.r :=
  uliftSplittingOfDown_r.{u, v} C S s

example (S : ShortComplex (ULift.{v} C))
    (s : (S.map (ULift.downFunctor : ULift.{v} C ⥤ C)).Splitting) :
    (uliftSplittingOfDown.{u, v} C S s).s = s.s :=
  uliftSplittingOfDown_s.{u, v} C S s

example :
    (∀ S : ShortComplex (ULift.{v} C), IsAdmissibleExact S → Nonempty S.Splitting) ↔
      (∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :=
  ulift_all_admissible_split_iff.{u, v} C

example :
    (ULift.upFunctor : C ⥤ ULift.{v} C).obj (0 : C) = Waldhausen.uliftZeroObject.{u, v} C :=
  Waldhausen.uliftZeroObject_up.{u, v} C

example :
    (ULift.downFunctor : ULift.{v} C ⥤ C).obj (Waldhausen.uliftZeroObject.{u, v} C) = (0 : C) :=
  Waldhausen.uliftZeroObject_down.{u, v} C

example :
    (Waldhausen.uliftZeroObjectIsoZero.{u, v} C).hom =
      (isZero_zero C).to_ ((0 : ULift.{v} C).down) :=
  Waldhausen.uliftZeroObjectIsoZero_hom.{u, v} C

example :
    (Waldhausen.uliftZeroObjectIsoZero.{u, v} C).inv =
      (isZero_zero C).from_ ((0 : ULift.{v} C).down) :=
  Waldhausen.uliftZeroObjectIsoZero_inv.{u, v} C

example :
    letI := ExactCategory.waldhausenCategory C
    ExactCategory.waldhausenCategory (ULift.{v} C) = Waldhausen.uliftWaldhausenCategory.{u, v} C :=
  ulift_waldhausenCategory_eq.{u, v} C

end Generic

section HigherHomWorld

variable (C : Type) [Category.{1} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]

local instance : Preadditive (ULift.{1} C) := uliftPreadditive.{0, 1} C
local instance : HasZeroObject (ULift.{1} C) := Waldhausen.uliftHasZeroObject.{0, 1} C
local instance : HasBinaryBiproducts (ULift.{1} C) := uliftHasBinaryBiproducts.{0, 1} C
local instance : ExactCategory (ULift.{1} C) := uliftExactCategory.{0, 1} C
local instance : (ULift.downFunctor : ULift.{1} C ⥤ C).Additive := uliftDown_additive.{0, 1} C

example (X Y : ULift.{1} C) : (X ⟶ Y) = (X.down ⟶ Y.down) := rfl

example (S : ShortComplex (ULift.{1} C)) :
    IsAdmissibleExact S ↔ IsAdmissibleExact (S.map (ULift.downFunctor : ULift.{1} C ⥤ C)) :=
  ulift_isAdmissibleExact_iff.{0, 1} C S

example : (ULift.downFunctor : ULift.{1} C ⥤ C).IsExact := uliftDown_isExact.{0, 1} C

end HigherHomWorld

#print axioms CategoryTheory.ExactCategory.uliftDownFullyFaithful
#print axioms CategoryTheory.ExactCategory.uliftPreadditive
#print axioms CategoryTheory.ExactCategory.uliftDown_additive
#print axioms CategoryTheory.ExactCategory.uliftUp_additive
#print axioms CategoryTheory.ExactCategory.uliftHasBinaryBiproducts
#print axioms CategoryTheory.ExactCategory.uliftUp_down_mapShortComplex
#print axioms CategoryTheory.ExactCategory.uliftDown_up_shortComplexIso
#print axioms CategoryTheory.ExactCategory.ulift_shortExact_iff
#print axioms CategoryTheory.ExactCategory.uliftSplittingOfDown
#print axioms CategoryTheory.ExactCategory.uliftSplittingOfDown_r
#print axioms CategoryTheory.ExactCategory.uliftSplittingOfDown_s
#print axioms CategoryTheory.ExactCategory.ulift_splitting_iff
#print axioms CategoryTheory.ExactCategory.uliftExactCategory
#print axioms CategoryTheory.ExactCategory.ulift_isAdmissibleExact_iff
#print axioms CategoryTheory.ExactCategory.ulift_isAdmissibleMono_iff
#print axioms CategoryTheory.ExactCategory.ulift_isAdmissibleEpi_iff
#print axioms CategoryTheory.ExactCategory.uliftUp_isAdmissibleExact_iff
#print axioms CategoryTheory.ExactCategory.uliftDown_isExact
#print axioms CategoryTheory.ExactCategory.uliftUp_isExact
#print axioms CategoryTheory.ExactCategory.ulift_all_admissible_split_iff
#print axioms CategoryTheory.ExactCategory.ulift_waldhausen_cofibrations
#print axioms CategoryTheory.ExactCategory.ulift_waldhausen_weakEquivalences
#print axioms CategoryTheory.ExactCategory.ulift_waldhausenCategory_eq

#lint only unusedArguments in MathlibExt.CategoryTheory.ExactCategory.ULift

end ExactCategoryULiftTests
