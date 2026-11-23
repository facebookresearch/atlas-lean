/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Colimit preservation for braided tensor functors

In a braided monoidal category, transports preservation of colimits from
tensoring on the left by a fixed object to tensoring on the right by that
object. The argument uses the braiding to identify the two tensor functors.
-/

@[expose] public section

open CategoryTheory Limits

universe v u w w'

namespace CategoryTheory.MonoidalCategory.Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- In a braided monoidal category, if tensoring on the left by `X` preserves
colimits of a given size, then tensoring on the right by `X` does too. -/
instance preservesColimitsOfSize_of_braided_and_preservesColimitsOfSize_tensor_left
    (X : C) [PreservesColimitsOfSize.{w, w'} (tensorLeft X)] :
    PreservesColimitsOfSize.{w, w'} (tensorRight X) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

end CategoryTheory.MonoidalCategory.Limits
