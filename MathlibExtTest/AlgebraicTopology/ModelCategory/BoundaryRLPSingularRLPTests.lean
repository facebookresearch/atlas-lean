/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.BoundaryRLPSingularRLP

@[expose] public section

/-!
# Boundary-RLP singular transport client

Thin public client for `TopCat.boundaryRLP_toSSet_mem_I_rlp` and
`TopCat.boundaryRLP_le_inverseImage_I_rlp` by term application only.
No `SSet.I.rlp` weak-equivalence, `TopCat` weak-equivalence, or model-structure claim.
-/

set_option autoImplicit false

open CategoryTheory

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.BoundaryRLPSingularRLPTests

theorem mem_client {X Y : TopCat.{0}} {f : X ⟶ Y}
    (hf : TopCat.realizedBoundaryInclusions.rlp f)
    {A B : SSet.{0}} {i : A ⟶ B}
    (hi : SSet.modelCategoryQuillen.I i) :
    HasLiftingProperty i (TopCat.toSSet.map f) :=
  TopCat.boundaryRLP_toSSet_mem_I_rlp hf hi

theorem le_client :
    TopCat.realizedBoundaryInclusions.{0}.rlp ≤
      (SSet.modelCategoryQuillen.I.{0}.rlp).inverseImage TopCat.toSSet :=
  TopCat.boundaryRLP_le_inverseImage_I_rlp

#print axioms TopCat.boundaryRLP_toSSet_mem_I_rlp
#print axioms TopCat.boundaryRLP_le_inverseImage_I_rlp
#print axioms mem_client
#print axioms le_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.BoundaryRLPSingularRLPTests
