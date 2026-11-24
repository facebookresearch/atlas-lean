/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorSmallObject

@[expose] public section

/-!
# Realized generator small-object cardinal client

Minimal public client for `TopCatGeneratorSmallObject`: Lean infers the
`IsCardinalForSmallObjectArgument` instance for the realized generator union
at `realizedGeneratorCardinal`. No further claim is made here.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatGeneratorSmallObjectTests

universe u

#check (inferInstance :
    CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument
      (TopCat.realizedBoundaryInclusions.{u} ⊔ TopCat.realizedHornInclusions.{u})
      realizedGeneratorCardinal.{u})
#synth CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument
  (TopCat.realizedBoundaryInclusions.{u} ⊔ TopCat.realizedHornInclusions.{u})
  realizedGeneratorCardinal.{u}

example :
    CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument
      (TopCat.realizedBoundaryInclusions.{u} ⊔ TopCat.realizedHornInclusions.{u})
      realizedGeneratorCardinal.{u} :=
  inferInstance

end TopCatGeneratorSmallObjectTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
