/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorSmallObjectInputs

@[expose] public section

/-!
# Small-object structural-input client

Minimal public client for `TopCatGeneratorSmallObjectInputs`: the bottom
element on the generator cardinal index type and smallness of the generator
union. No further claim is made here.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatGeneratorSmallObjectInputsTests

universe u

#check (inferInstance : OrderBot realizedGeneratorCardinal.{u}.ord.ToType)
#synth OrderBot realizedGeneratorCardinal.{u}.ord.ToType

#check (inferInstance :
    CategoryTheory.MorphismProperty.IsSmall.{u}
      (TopCat.realizedBoundaryInclusions.{u} ⊔
        TopCat.realizedHornInclusions.{u}))
#synth CategoryTheory.MorphismProperty.IsSmall.{u}
  (TopCat.realizedBoundaryInclusions.{u} ⊔ TopCat.realizedHornInclusions.{u})

noncomputable example : OrderBot realizedGeneratorCardinal.{u}.ord.ToType :=
  inferInstance

example :
    CategoryTheory.MorphismProperty.IsSmall.{u}
      (TopCat.realizedBoundaryInclusions.{u} ⊔
        TopCat.realizedHornInclusions.{u}) :=
  inferInstance

end TopCatGeneratorSmallObjectInputsTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
