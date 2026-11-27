/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyFactorization

/-!
# Tests for Reedy factorization of simplicial morphisms
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
variable (P Q : MorphismProperty C)
variable [P.HasFactorization Q] [P.RespectsIso] [Q.RespectsIso]
variable {X Y : SimplicialObject C} (f : X ⟶ Y)

example : (reedyLeft P).MapFactorizationData (reedyRight Q) f :=
  reedyMapFactorizationData f P Q

example : SimplicialObject C :=
  (reedyMapFactorizationData f P Q).Z

example : X ⟶ (reedyMapFactorizationData f P Q).Z :=
  (reedyMapFactorizationData f P Q).i

example : (reedyMapFactorizationData f P Q).Z ⟶ Y :=
  (reedyMapFactorizationData f P Q).p

example :
    (reedyMapFactorizationData f P Q).i ≫
        (reedyMapFactorizationData f P Q).p = f :=
  (reedyMapFactorizationData f P Q).fac

example : reedyLeft P (reedyMapFactorizationData f P Q).i :=
  (reedyMapFactorizationData f P Q).hi

example : reedyRight Q (reedyMapFactorizationData f P Q).p :=
  (reedyMapFactorizationData f P Q).hp

example :
    (reedyMapFactorizationData f P Q).Z =
      (ReedyStructure.DegreeFactorization.classifiedFactor reedyStructure f
        (P.factorizationData Q)).Z :=
  rfl

example :
    (reedyMapFactorizationData f P Q).i =
      (ReedyStructure.DegreeFactorization.classifiedFactor reedyStructure f
        (P.factorizationData Q)).i :=
  rfl

example :
    (reedyMapFactorizationData f P Q).p =
      (ReedyStructure.DegreeFactorization.classifiedFactor reedyStructure f
        (P.factorizationData Q)).p :=
  rfl

#synth (reedyLeft P).HasFactorization (reedyRight Q)

end Positive

section MissingBaseFactorization

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C] [HasPullbacks C]
variable [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
variable [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
variable (P Q : MorphismProperty C)
variable [P.RespectsIso] [Q.RespectsIso]

#guard_msgs (error, substring := true) in
example : (reedyLeft P).HasFactorization (reedyRight Q) := inferInstance

end MissingBaseFactorization

section MissingLeftIsoRespect

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C] [HasPullbacks C]
variable [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
variable [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
variable (P Q : MorphismProperty C)
variable [P.HasFactorization Q] [Q.RespectsIso]

#guard_msgs (error, substring := true) in
example : (reedyLeft P).HasFactorization (reedyRight Q) := inferInstance

end MissingLeftIsoRespect

section MissingRightIsoRespect

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C] [HasPullbacks C]
variable [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
variable [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
variable (P Q : MorphismProperty C)
variable [P.HasFactorization Q] [P.RespectsIso]

#guard_msgs (error, substring := true) in
example : (reedyLeft P).HasFactorization (reedyRight Q) := inferInstance

end MissingRightIsoRespect

section PrivateHelpers

#guard_msgs (error, substring := true) in
#check
  CategoryTheory.SimplicialObject.ReedyR4OneDegreeFunctorPreflight.globalRelativeLatchingArrowIso

end PrivateHelpers

section Nonclaims

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyFunctorialFactorization

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyWeakFactorizationSystem

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyModelCategory

end Nonclaims

#print axioms CategoryTheory.SimplicialObject.reedyMapFactorizationData
#print axioms CategoryTheory.SimplicialObject.reedyHasFactorization

end CategoryTheory.SimplicialObject
