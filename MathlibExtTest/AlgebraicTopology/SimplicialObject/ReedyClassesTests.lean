/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyStructure

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable (P : MorphismProperty C)

section Left

variable [HasPushouts C]
variable [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]

example {X Y : SimplicialObject C} (f : X ⟶ Y) :
    reedyLeft P f ↔ ∀ n : ℕ, P (relativeLatchingMap f n) :=
  reedyLeft_iff P f

example {X Y : SimplicialObject C} {f : X ⟶ Y}
    (hf : reedyLeft P f) : P (relativeLatchingMap f 0) :=
  hf 0

section Identities

variable [P.ContainsIdentities] [P.RespectsIso]

example : (reedyLeft P).ContainsIdentities := inferInstance

example (X : SimplicialObject C) : reedyLeft P (𝟙 X) :=
  (reedyLeft P).id_mem X

end Identities

section Retracts

variable [P.IsStableUnderRetracts]

example : (reedyLeft P).IsStableUnderRetracts := inferInstance

example : (reedyLeft P).RespectsIso := inferInstance

example {X Y Z W : SimplicialObject C}
    {f : X ⟶ Y} {g : Z ⟶ W}
    (h : RetractArrow f g) (hg : reedyLeft P g) :
    reedyLeft P f :=
  MorphismProperty.of_retract h hg

end Retracts

section MissingRespectsIso

variable [P.ContainsIdentities]

#guard_msgs (error, substring := true) in
example : (reedyLeft P).ContainsIdentities := inferInstance

end MissingRespectsIso

section MissingContainsIdentities

variable [P.RespectsIso]

#guard_msgs (error, substring := true) in
example : (reedyLeft P).ContainsIdentities := inferInstance

end MissingContainsIdentities

#guard_msgs (error, substring := true) in
example : (reedyLeft P).IsStableUnderRetracts := inferInstance

section MultiplicativityNonclaim

variable [P.IsMultiplicative] [P.RespectsIso]

#guard_msgs (error, substring := true) in
example : (reedyLeft P).IsStableUnderComposition := inferInstance

end MultiplicativityNonclaim

end Left


section Right

variable [HasPullbacks C]
variable [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]

example {X Y : SimplicialObject C} (f : X ⟶ Y) :
    reedyRight P f ↔ ∀ n : ℕ, P (relativeMatchingMap f n) :=
  reedyRight_iff P f

example {X Y : SimplicialObject C} {f : X ⟶ Y}
    (hf : reedyRight P f) : P (relativeMatchingMap f 0) :=
  hf 0

section Identities

variable [P.ContainsIdentities] [P.RespectsIso]

example : (reedyRight P).ContainsIdentities := inferInstance

example (X : SimplicialObject C) : reedyRight P (𝟙 X) :=
  (reedyRight P).id_mem X

end Identities

section Retracts

variable [P.IsStableUnderRetracts]

example : (reedyRight P).IsStableUnderRetracts := inferInstance

example : (reedyRight P).RespectsIso := inferInstance

example {X Y Z W : SimplicialObject C}
    {f : X ⟶ Y} {g : Z ⟶ W}
    (h : RetractArrow f g) (hg : reedyRight P g) :
    reedyRight P f :=
  MorphismProperty.of_retract h hg

end Retracts

section MissingRespectsIso

variable [P.ContainsIdentities]

#guard_msgs (error, substring := true) in
example : (reedyRight P).ContainsIdentities := inferInstance

end MissingRespectsIso

section MissingContainsIdentities

variable [P.RespectsIso]

#guard_msgs (error, substring := true) in
example : (reedyRight P).ContainsIdentities := inferInstance

end MissingContainsIdentities

#guard_msgs (error, substring := true) in
example : (reedyRight P).IsStableUnderRetracts := inferInstance

section MultiplicativityNonclaim

variable [P.IsMultiplicative] [P.RespectsIso]

#guard_msgs (error, substring := true) in
example : (reedyRight P).IsStableUnderComposition := inferInstance

end MultiplicativityNonclaim

end Right


#print axioms reedyLeft
#print axioms reedyRight
#print axioms CategoryTheory.SimplicialObject.instContainsIdentitiesReedyLeftOfRespectsIso
#print axioms CategoryTheory.SimplicialObject.instContainsIdentitiesReedyRightOfRespectsIso
#print axioms CategoryTheory.SimplicialObject.instIsStableUnderRetractsReedyLeft
#print axioms CategoryTheory.SimplicialObject.instIsStableUnderRetractsReedyRight

end CategoryTheory.SimplicialObject
