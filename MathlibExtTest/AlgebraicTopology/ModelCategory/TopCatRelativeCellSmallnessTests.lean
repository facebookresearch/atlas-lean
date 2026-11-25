/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatBoundaryRelativeCellSmallness
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornRelativeCellSmallness

@[expose] public section

/-!
# Split relative-cell smallness client

Minimal public client for the split boundary and horn relative-cell
providers: Lean infers the two `IsCardinalForSmallObjectArgument`
instances for realized boundary and horn inclusions at
`realizedGeneratorCardinal`. No further claim is made here.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatRelativeCellSmallnessTests

universe u

#check (inferInstance :
    CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument
      TopCat.realizedBoundaryInclusions.{u} realizedGeneratorCardinal.{u})
#synth CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument
  TopCat.realizedBoundaryInclusions.{u} realizedGeneratorCardinal.{u}

#check (inferInstance :
    CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument
      TopCat.realizedHornInclusions.{u} realizedGeneratorCardinal.{u})
#synth CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument
  TopCat.realizedHornInclusions.{u} realizedGeneratorCardinal.{u}

theorem boundaryCardinal_client :
    CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument
      TopCat.realizedBoundaryInclusions.{u} realizedGeneratorCardinal.{u} :=
  inferInstance

theorem hornCardinal_client :
    CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument
      TopCat.realizedHornInclusions.{u} realizedGeneratorCardinal.{u} :=
  inferInstance

#print axioms preservesColimit_coyoneda_of_relativeCellComplex_boundary
#print axioms preservesColimit_coyoneda_of_relativeCellComplex_horn
#print axioms boundaryCardinal_client
#print axioms hornCardinal_client

end TopCatRelativeCellSmallnessTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
