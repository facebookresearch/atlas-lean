/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PushoutJoinGeneratedLifting

/-!
# Tests for generated pushout-join lifting classes
-/

set_option autoImplicit false

open CategoryTheory

universe u

namespace SSet

example (P Q R : MorphismProperty SSet.{u})
    (hfree : ∀ ⦃A B K L : SSet.{u}⦄ (i : A ⟶ B), P i →
      ∀ (j : K ⟶ L), Q j →
        R.rlp.llp (joinUnderPushoutObjObj i j).ι)
    {A B K L : SSet.{u}} {i : A ⟶ B} {j : K ⟶ L}
    (hi : P.rlp.llp i) (hj : Q.rlp.llp j) :
    R.rlp.llp (joinUnderPushoutObjObj i j).ι :=
  pushoutJoin_mem_rlp_llp P Q R hfree hi hj

end SSet
