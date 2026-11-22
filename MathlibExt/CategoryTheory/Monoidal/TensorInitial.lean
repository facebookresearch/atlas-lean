/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Initial objects under tensoring in a braided closed category

The selected initial object remains initial under tensoring on either side.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
namespace CategoryTheory.MonoidalCategory
open Limits BraidedCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasInitial C]

omit [BraidedCategory C] in
/-- Fixed-left tensoring preserves the selected initial object. -/
def tensorInitialLeft (X : C) : IsInitial (X ⊗ ⊥_ C) := by
  let _ : PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (ihom.adjunction X).leftAdjoint_preservesColimits
  exact IsInitial.isInitialObj (tensorLeft X) (⊥_ C) initialIsInitial

/-- Fixed-right tensoring preserves the selected initial object. -/
def tensorInitialRight (X : C) : IsInitial ((⊥_ C) ⊗ X) := by
  let _ : PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (ihom.adjunction X).leftAdjoint_preservesColimits
  let _ : PreservesColimit (Functor.empty.{0} C) (tensorRight X) :=
    preservesColimit_of_natIso (Functor.empty.{0} C) (tensorLeftIsoTensorRight X)
  exact IsInitial.isInitialObj (tensorRight X) (⊥_ C) initialIsInitial

end CategoryTheory.MonoidalCategory
