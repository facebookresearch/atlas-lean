/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornWFS

/-!
# Horn weak factorization client

Thin direct client synthesizing the `IsWeakFactorizationSystem` instance for the
realized horn pair by term application only. States no further claim.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatHornWFSTests

universe u

#check (inferInstance :
    CategoryTheory.MorphismProperty.IsWeakFactorizationSystem
      (TopCat.realizedHornInclusions.{u}).rlp.llp
      (TopCat.realizedHornInclusions.{u}).rlp)

#synth CategoryTheory.MorphismProperty.IsWeakFactorizationSystem
  (TopCat.realizedHornInclusions.{u}).rlp.llp
  (TopCat.realizedHornInclusions.{u}).rlp

theorem hornWFS_client :
    CategoryTheory.MorphismProperty.IsWeakFactorizationSystem
      (TopCat.realizedHornInclusions.{u}).rlp.llp
      (TopCat.realizedHornInclusions.{u}).rlp :=
  inferInstance

#print axioms hornWFS_client

end TopCatHornWFSTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
