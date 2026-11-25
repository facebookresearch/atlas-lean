/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Monoidal.RightModuleMappingEnd

/-!
# Components of the original source mapping comparison

The actual natural comparison of the right-module source equalizer with the
stock internal Hom has the original limiting-fork module isomorphism as each
component. Both full comparison maps are retained.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.CommutativeModuleConversion
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.RightModuleMappingEnd

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [HasEqualizers C]
  (R : C) [MonObj R] [IsCommMonObj R]

/-- Every full natural-comparison component is the original limiting-fork module iso. -/
theorem comparisonNatIso_app (M N : RightModule R) :
    (comparisonNatIso R M).app N = moduleComparison R M N := rfl

/-- The full forward component is the original forward module comparison. -/
theorem comparisonNatIso_hom_app (M N : RightModule R) :
    (comparisonNatIso R M).hom.app N = (moduleComparison R M N).hom :=
  congrArg Iso.hom (comparisonNatIso_app R M N)

/-- The full inverse component is the original inverse module comparison. -/
theorem comparisonNatIso_inv_app (M N : RightModule R) :
    (comparisonNatIso R M).inv.app N = (moduleComparison R M N).inv :=
  congrArg Iso.inv (comparisonNatIso_app R M N)

/-- The original source functor chooses the entire constructed source equalizer module. -/
theorem functor_obj (M N : RightModule R) :
    (functor R M).obj N = moduleObject R M N := rfl

/-- The original converted stock functor chooses the entire original stock Hom module. -/
theorem stockFunctor_obj (M N : RightModule R) :
    (stockFunctor R M).obj N = stockRightHom R M N := rfl

end CategoryTheory.RightModuleMappingEnd
