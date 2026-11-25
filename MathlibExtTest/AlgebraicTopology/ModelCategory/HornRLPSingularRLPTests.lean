/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.HornRLPSingularRLP

@[expose] public section

/-!
# Horn-RLP singular transport client

Thin public client for `TopCat.hornRLP_iff_toSSet_mem_J_rlp` and
`TopCat.hornRLP_eq_inverseImage_J_rlp` by term application only.
No `SSet.J.rlp` weak-equivalence, `TopCat` weak-equivalence, or model-structure claim.
-/

set_option autoImplicit false

open CategoryTheory

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.HornRLPSingularRLPTests

theorem iff_client {X Y : TopCat.{0}} {f : X ⟶ Y} :
    TopCat.realizedHornInclusions.rlp f ↔
      SSet.modelCategoryQuillen.J.rlp (TopCat.toSSet.map f) :=
  TopCat.hornRLP_iff_toSSet_mem_J_rlp

theorem eq_client :
    TopCat.realizedHornInclusions.{0}.rlp =
      (SSet.modelCategoryQuillen.J.{0}.rlp).inverseImage TopCat.toSSet :=
  TopCat.hornRLP_eq_inverseImage_J_rlp

theorem forward_client {X Y : TopCat.{0}} {f : X ⟶ Y} {A B : SSet.{0}} {i : A ⟶ B}
    (hf : TopCat.realizedHornInclusions.rlp f)
    (hi : SSet.modelCategoryQuillen.J i) :
    HasLiftingProperty i (TopCat.toSSet.map f) :=
  TopCat.hornRLP_toSSet_mem_J_rlp hf hi

theorem reverse_client {X Y : TopCat.{0}} {f : X ⟶ Y}
    (hf : SSet.modelCategoryQuillen.J.rlp (TopCat.toSSet.map f)) :
    TopCat.realizedHornInclusions.rlp f :=
  TopCat.mem_hornRLP_of_toSSet_mem_J_rlp hf

#print axioms TopCat.hornRLP_iff_toSSet_mem_J_rlp
#print axioms TopCat.hornRLP_eq_inverseImage_J_rlp
#print axioms iff_client
#print axioms eq_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.HornRLPSingularRLPTests
