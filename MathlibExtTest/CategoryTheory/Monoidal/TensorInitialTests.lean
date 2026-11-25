/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Monoidal.TensorInitial
set_option autoImplicit false
noncomputable section
universe u v
namespace MathlibExtTest.TensorInitial
open CategoryTheory Limits MonoidalCategory
example {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [MonoidalClosed C] [HasInitial C] (X : C) : IsInitial (X ⊗ ⊥_ C) :=
  tensorInitialLeft X
example {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C] [HasInitial C] (X : C) : IsInitial ((⊥_ C) ⊗ X) :=
  tensorInitialRight X
#check @tensorInitialLeft
#check @tensorInitialRight
#print axioms tensorInitialLeft
#print axioms tensorInitialRight
end MathlibExtTest.TensorInitial
