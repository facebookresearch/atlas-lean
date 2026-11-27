/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyLifting

/-!
# Tests for degreewise Reedy lifting
-/

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C] [HasPullbacks C]
variable [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
variable [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
variable (P Q : MorphismProperty C)

example (hPQ : P ≤ Q.llp) :
    reedyLeft P ≤ (reedyRight Q).llp :=
  reedyLeft_le_llp_reedyRight P Q hPQ

section Application

variable {A B E F : SimplicialObject C}
variable (i : A ⟶ B) (p : E ⟶ F)

example (hPQ : P ≤ Q.llp) (hi : reedyLeft P i) (hp : reedyRight Q p) :
    HasLiftingProperty i p :=
  reedyLeft_le_llp_reedyRight P Q hPQ i hi p hp

#guard_msgs (error, substring := true) in
example (hi : reedyLeft P i) (hp : reedyRight Q p) :
    HasLiftingProperty i p :=
  reedyLeft_le_llp_reedyRight P Q i hi p hp

end Application

section PrivateHelpers

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.lowerLatchingCocone

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.extensionData

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.globalLift

end PrivateHelpers

#print axioms CategoryTheory.SimplicialObject.reedyLeft_le_llp_reedyRight

end CategoryTheory.SimplicialObject
