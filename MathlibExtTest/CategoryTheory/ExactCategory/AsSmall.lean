/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ExactCategory.AsSmall
public import Batteries.Tactic.Lint

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

namespace ExactCategoryAsSmallTests

universe u v l

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]

local instance : Preadditive (AsSmall.{l} C) := asSmallPreadditive.{u, v, l} C
local instance : HasZeroObject (AsSmall.{l} C) := asSmallHasZeroObject.{u, v, l} C
local instance : HasBinaryBiproducts (AsSmall.{l} C) := asSmallHasBinaryBiproducts.{u, v, l} C
local instance : ExactCategory (AsSmall.{l} C) := asSmallExactCategory.{u, v, l} C
local instance : (AsSmall.up : C ⥤ AsSmall.{l} C).Additive := asSmallUp_additive.{u, v, l} C
local instance : (AsSmall.down : AsSmall.{l} C ⥤ C).Additive := asSmallDown_additive.{u, v, l} C

example {X Y : C} (f : X ⟶ Y) :
    ((AsSmall.up : C ⥤ AsSmall.{l} C).map f).down = f := rfl

example (S : ShortComplex C) :
    (S.map (AsSmall.up : C ⥤ AsSmall.{l} C)).map (AsSmall.down : AsSmall.{l} C ⥤ C) = S :=
  asSmallUp_down_mapShortComplex.{u, v, l} C S

example (S : ShortComplex (AsSmall.{l} C)) :
    IsAdmissibleExact S ↔ IsAdmissibleExact (S.map (AsSmall.down : AsSmall.{l} C ⥤ C)) :=
  asSmall_isAdmissibleExact_iff.{u, v, l} C S

example :
    (∀ S : ShortComplex (AsSmall.{l} C), IsAdmissibleExact S → Nonempty S.Splitting) ↔
      (∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :=
  asSmall_all_admissible_split_iff.{u, v, l} C

example (S : ShortComplex (AsSmall.{l} C))
    (s : (S.map (AsSmall.down : AsSmall.{l} C ⥤ C)).Splitting) :
    ULift.down (asSmallSplittingOfDown.{u, v, l} C S s).r = s.r :=
  asSmallSplittingOfDown_r_down.{u, v, l} C S s

example (S : ShortComplex (AsSmall.{l} C))
    (s : (S.map (AsSmall.down : AsSmall.{l} C ⥤ C)).Splitting) :
    ULift.down (asSmallSplittingOfDown.{u, v, l} C S s).s = s.s :=
  asSmallSplittingOfDown_s_down.{u, v, l} C S s

example :
    ULift.down (asSmallUpZeroIso.{u, v, l} C).hom =
      (isZero_zero C).to_ (ULift.down (0 : AsSmall.{l} C)) :=
  asSmallUpZeroIso_hom_down.{u, v, l} C

example :
    ULift.down (asSmallUpZeroIso.{u, v, l} C).inv =
      (isZero_zero C).from_ (ULift.down (0 : AsSmall.{l} C)) :=
  asSmallUpZeroIso_inv_down.{u, v, l} C

#print axioms CategoryTheory.ExactCategory.asSmallDownFullyFaithful
#print axioms CategoryTheory.ExactCategory.asSmallPreadditive
#print axioms CategoryTheory.ExactCategory.asSmallDown_additive
#print axioms CategoryTheory.ExactCategory.asSmallUp_additive
#print axioms CategoryTheory.ExactCategory.asSmallHasZeroObject
#print axioms CategoryTheory.ExactCategory.asSmallUpZeroIso
#print axioms CategoryTheory.ExactCategory.asSmallUpZeroIso_hom_down
#print axioms CategoryTheory.ExactCategory.asSmallUpZeroIso_inv_down
#print axioms CategoryTheory.ExactCategory.asSmallHasBinaryBiproducts
#print axioms CategoryTheory.ExactCategory.asSmallExactCategory
#print axioms CategoryTheory.ExactCategory.asSmall_isAdmissibleExact_iff
#print axioms CategoryTheory.ExactCategory.asSmallUp_down_mapShortComplex
#print axioms CategoryTheory.ExactCategory.asSmallUp_isAdmissibleExact_iff
#print axioms CategoryTheory.ExactCategory.asSmallDown_isExact
#print axioms CategoryTheory.ExactCategory.asSmallUp_isExact
#print axioms CategoryTheory.ExactCategory.asSmallDown_up_shortComplexIso
#print axioms CategoryTheory.ExactCategory.asSmallSplittingOfDown
#print axioms CategoryTheory.ExactCategory.asSmallSplittingOfDown_r_down
#print axioms CategoryTheory.ExactCategory.asSmallSplittingOfDown_s_down
#print axioms CategoryTheory.ExactCategory.asSmall_splitting_iff
#print axioms CategoryTheory.ExactCategory.asSmall_all_admissible_split_iff

#lint only unusedArguments in MathlibExt.CategoryTheory.ExactCategory.AsSmall

end ExactCategoryAsSmallTests
