/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Limits.Arrow

/-!
# Tests for arrow projection limit preservation
-/

@[expose] public section

noncomputable section

universe v u vJ uJ

open CategoryTheory Limits

namespace CategoryTheory.ArrowTest

variable {C : Type u} [Category.{v} C]
variable {J : Type uJ} [Category.{vJ} J] [HasLimitsOfShape J C]

example : PreservesLimitsOfShape J (Arrow.leftFunc : Arrow C ⥤ C) :=
  inferInstance

example : PreservesLimitsOfShape J (Arrow.rightFunc : Arrow C ⥤ C) :=
  inferInstance

example {F : J ⥤ Arrow C} (c : Cone F) (hc : IsLimit c) :
    IsLimit (Arrow.leftFunc.mapCone c) :=
  isLimitOfPreserves Arrow.leftFunc hc

example {F : J ⥤ Arrow C} (c : Cone F) (hc : IsLimit c) :
    IsLimit (Arrow.rightFunc.mapCone c) :=
  isLimitOfPreserves Arrow.rightFunc hc

end CategoryTheory.ArrowTest
