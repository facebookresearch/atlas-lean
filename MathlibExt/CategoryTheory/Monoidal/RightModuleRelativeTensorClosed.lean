/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Monoidal.RightModuleRelativeTensor
public import MathlibExt.CategoryTheory.Monoidal.Mod.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Transport

/-!
# Closedness of the stock right-module relative tensor

The closed structure is transported once through the original module conversion
from the existing Mod internal Hom and its selected adjunction.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.CommutativeModuleConversion (RightModule)
open scoped CategoryTheory.MonObj

namespace CategoryTheory.RightModuleFree

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable (M : C) [MonObj M] [SymmetricCategory C] [IsCommMonObj M]
variable [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]

/-- The selected closed structure uses the original complete conversion equivalence. -/
@[instance_reducible]
def tensorClosed : @MonoidalClosed (RightModule M) _ (tensorMonoidal M) := by
  letI : MonoidalCategory (Mod C M) := Mod.instMonoidalCategory (scalarCommMon M)
  letI : MonoidalClosed (Mod C M) := Mod.instMonoidalClosed (scalarCommMon M)
  exact inferInstanceAs
    (MonoidalClosed
      (Monoidal.Transported (CommutativeModuleConversion.moduleEquivalence M)))

end CategoryTheory.RightModuleFree
