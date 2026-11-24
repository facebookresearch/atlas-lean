/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatBoundaryWFS

/-!
# Boundary weak factorization client

Thin direct client synthesizing the `IsWeakFactorizationSystem` instance for
realized boundary inclusions by term application only. States no further claim.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatBoundaryWFSTests

universe u

#check (inferInstance :
    CategoryTheory.MorphismProperty.IsWeakFactorizationSystem
      (TopCat.realizedBoundaryInclusions.{u}).rlp.llp
      (TopCat.realizedBoundaryInclusions.{u}).rlp)

#synth CategoryTheory.MorphismProperty.IsWeakFactorizationSystem
  (TopCat.realizedBoundaryInclusions.{u}).rlp.llp
  (TopCat.realizedBoundaryInclusions.{u}).rlp

theorem boundaryWFS_client :
    CategoryTheory.MorphismProperty.IsWeakFactorizationSystem
      (TopCat.realizedBoundaryInclusions.{u}).rlp.llp
      (TopCat.realizedBoundaryInclusions.{u}).rlp :=
  inferInstance

#print axioms boundaryWFS_client

end TopCatBoundaryWFSTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
