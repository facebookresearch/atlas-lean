/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section

open CategoryTheory Limits

universe v u w w'

namespace CategoryTheory.MonoidalCategory.Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Let `C` be a braided monoidal category and `X ∈ C`. If the
left tensor functor `X ⊗ -` preserves colimits of diagram size
`(w,w′)`, the right tensor functor `- ⊗ X` preserves colimits of
that same size, by the braiding comparison between the two functors. -/
instance preservesColimitsOfSize_of_braided_and_preservesColimitsOfSize_tensor_left
    (X : C) [PreservesColimitsOfSize.{w, w'} (tensorLeft X)] :
    PreservesColimitsOfSize.{w, w'} (tensorRight X) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

end CategoryTheory.MonoidalCategory.Limits
