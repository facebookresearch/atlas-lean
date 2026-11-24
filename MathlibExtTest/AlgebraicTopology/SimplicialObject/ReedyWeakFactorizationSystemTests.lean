/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyWeakFactorizationSystem

/-!
# Tests for Reedy weak factorization systems
-/

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace CategoryTheory.SimplicialObject

section Positive

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C] [HasPullbacks C]
variable [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
variable [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
variable (P Q : MorphismProperty C) [P.IsWeakFactorizationSystem Q]

#synth (reedyLeft P).IsWeakFactorizationSystem (reedyRight Q)

example : (reedyRight Q).llp = reedyLeft P :=
  llp_eq_of_wfs (reedyLeft P) (reedyRight Q)

example : (reedyLeft P).rlp = reedyRight Q :=
  rlp_eq_of_wfs (reedyLeft P) (reedyRight Q)

example : (reedyLeft P).HasFactorization (reedyRight Q) := inferInstance

section Lifting

variable {A B X Y : SimplicialObject C}
variable (i : A ⟶ B) (p : X ⟶ Y)

example (hi : reedyLeft P i) (hp : reedyRight Q p) :
    HasLiftingProperty i p :=
  hasLiftingProperty_of_wfs i p hi hp

end Lifting

end Positive

section MissingBaseWFS

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C] [HasPullbacks C]
variable [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
variable [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
variable (P Q : MorphismProperty C)

#guard_msgs (error, substring := true) in
example : (reedyLeft P).IsWeakFactorizationSystem (reedyRight Q) := inferInstance

end MissingBaseWFS

section BaseFactorizationOnly

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C] [HasPullbacks C]
variable [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
variable [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
variable (P Q : MorphismProperty C)
variable [P.HasFactorization Q] [P.RespectsIso] [Q.RespectsIso]

#synth (reedyLeft P).HasFactorization (reedyRight Q)

#guard_msgs (error, substring := true) in
example : (reedyLeft P).IsWeakFactorizationSystem (reedyRight Q) := inferInstance

end BaseFactorizationOnly

section Nonclaims

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyFunctorialFactorization

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyModelCategory

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyTrivialCofibration_eq

end Nonclaims

#print axioms CategoryTheory.SimplicialObject.reedyIsWeakFactorizationSystem

end CategoryTheory.SimplicialObject
