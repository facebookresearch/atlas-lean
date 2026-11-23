/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatBoundarySmallObject

@[expose] public section

/-!
# Boundary small-object argument client

Minimal public client for `TopCatBoundarySmallObject`: Lean infers the
`IsCardinalForSmallObjectArgument` and `HasSmallObjectArgument` instances for
the realized boundary inclusions at `realizedGeneratorCardinal`.
No further claim is made here.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatBoundarySmallObjectTests

universe u

theorem boundary_isCardinal_client :
    CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument
      TopCat.realizedBoundaryInclusions.{u} realizedGeneratorCardinal.{u} :=
  inferInstance

theorem boundary_hasSmallObject_client :
    CategoryTheory.MorphismProperty.HasSmallObjectArgument.{u}
      TopCat.realizedBoundaryInclusions.{u} :=
  inferInstance

#print axioms boundary_isCardinal_client
#print axioms boundary_hasSmallObject_client

end TopCatBoundarySmallObjectTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
