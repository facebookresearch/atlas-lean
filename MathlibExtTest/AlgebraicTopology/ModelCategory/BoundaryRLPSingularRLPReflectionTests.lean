/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.BoundaryRLPSingularRLPReflection

@[expose] public section

/-!
# Boundary-RLP reflection equality client

Thin public client for `TopCat.inverseImage_I_rlp_le_boundaryRLP` and
`TopCat.boundaryRLP_eq_inverseImage_I_rlp` by term application only.
No `SSet.I.rlp` weak-equivalence, `TopCat` weak-equivalence, or model-structure claim.
-/

set_option autoImplicit false

open CategoryTheory

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.BoundaryRLPSingularRLPReflectionTests

/-- Pointwise reflection: singular boundary-RLP maps lift against realized generators. -/
theorem mem_client {X Y : TopCat.{0}} {f : X ⟶ Y}
    (hf : (SSet.modelCategoryQuillen.I.rlp).inverseImage TopCat.toSSet f)
    {A B : TopCat.{0}} {g : A ⟶ B} (hg : TopCat.realizedBoundaryInclusions g) :
    HasLiftingProperty g f :=
  TopCat.toSSet_I_rlp_mem_boundaryRLP hf hg

/-- Reverse inclusion: singular inverse image of `I.rlp` is boundary-RLP. -/
theorem le_client :
    (SSet.modelCategoryQuillen.I.{0}.rlp).inverseImage TopCat.toSSet ≤
      TopCat.realizedBoundaryInclusions.{0}.rlp :=
  TopCat.inverseImage_I_rlp_le_boundaryRLP

/-- Equality: realized boundary-RLP is the singular inverse image of `I.rlp`. -/
theorem eq_client :
    TopCat.realizedBoundaryInclusions.{0}.rlp =
      (SSet.modelCategoryQuillen.I.{0}.rlp).inverseImage TopCat.toSSet :=
  TopCat.boundaryRLP_eq_inverseImage_I_rlp

#print axioms TopCat.inverseImage_I_rlp_le_boundaryRLP
#print axioms TopCat.boundaryRLP_eq_inverseImage_I_rlp
#print axioms le_client
#print axioms eq_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.BoundaryRLPSingularRLPReflectionTests
