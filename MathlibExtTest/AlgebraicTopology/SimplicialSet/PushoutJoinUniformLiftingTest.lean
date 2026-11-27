/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PushoutJoinUniformLifting

/-!
# Tests for uniform pushout-join lifting
-/

set_option autoImplicit false

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

example {K₀ K A B X S : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (q : X ⟶ S) :
    HasLiftingProperty (joinOverPushoutObjObj i a).ι q ↔
      ∀ (f : K ⟶ X),
        HasLiftingProperty a (sliceOver.restrictionComparison i f q) :=
  sliceOver.hasLiftingProperty_pushoutJoin_iff_forall i a q

example {K₀ K A B X S : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (q : X ⟶ S) :
    HasLiftingProperty (joinUnderPushoutObjObj i a).ι q ↔
      ∀ (f : K ⟶ X),
        HasLiftingProperty a (sliceUnder.restrictionComparison i f q) :=
  sliceUnder.hasLiftingProperty_pushoutJoin_iff_forall i a q

end SSet
