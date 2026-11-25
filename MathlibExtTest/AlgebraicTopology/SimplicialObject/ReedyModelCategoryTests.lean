/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyModelCategory

/-!
# Tests for the opt-in Reedy model category
-/

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty
open HomotopicalAlgebra
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

section ScopeOff

variable {C : Type u} [Category.{v} C] [ModelCategory C]

#guard_msgs (error, substring := true) in
#synth ModelCategory (SimplicialObject C)

#guard_msgs (error, substring := true) in
#synth CategoryWithWeakEquivalences (SimplicialObject C)

#guard_msgs (error, substring := true) in
#synth CategoryWithCofibrations (SimplicialObject C)

#guard_msgs (error, substring := true) in
#synth CategoryWithFibrations (SimplicialObject C)

example (_X : SimplicialObject C) : True := by
  fail_if_success
    let _ : IsCofibrant _X := inferInstance
  trivial

example : ModelCategory (SimplicialObject C) :=
  reedyModelCategory

end ScopeOff

section ScopeOn

open scoped CategoryTheory.SimplicialObject.reedyModelCategory

variable {C : Type u} [Category.{v} C] [ModelCategory C]

#synth ModelCategory (SimplicialObject C)
#synth CategoryWithWeakEquivalences (SimplicialObject C)
#synth CategoryWithCofibrations (SimplicialObject C)
#synth CategoryWithFibrations (SimplicialObject C)
#synth HasFiniteLimits (SimplicialObject C)
#synth HasFiniteColimits (SimplicialObject C)
#synth (weakEquivalences (SimplicialObject C)).HasTwoOutOfThreeProperty

example :
    (inferInstance : ModelCategory (SimplicialObject C)) = reedyModelCategory :=
  rfl

example :
    weakEquivalences (SimplicialObject C) =
      (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ :=
  rfl

example :
    cofibrations (SimplicialObject C) = reedyLeft (cofibrations C) :=
  rfl

example :
    fibrations (SimplicialObject C) = reedyRight (fibrations C) :=
  rfl

example :
    trivialCofibrations (SimplicialObject C) =
      reedyLeft (trivialCofibrations C) := by
  change reedyLeft (cofibrations C) ⊓
      (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ =
    reedyLeft (trivialCofibrations C)
  exact reedyLeft_trivialCofibrations_eq.symm

example :
    trivialFibrations (SimplicialObject C) =
      reedyRight (trivialFibrations C) := by
  change reedyRight (fibrations C) ⊓
      (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ =
    reedyRight (trivialFibrations C)
  exact reedyRight_trivialFibrations_eq.symm

section CofibrantObjects

variable (X : SimplicialObject C)

example [IsCofibrant X] :
    X.LatchingMapsIn (cofibrations C) :=
  (reedyModelCategory.isCofibrant_iff_latchingMapsIn X).mp inferInstance

example (hX : X.LatchingMapsIn (cofibrations C)) :
    IsCofibrant X :=
  (reedyModelCategory.isCofibrant_iff_latchingMapsIn X).mpr hX

example [IsCofibrant X] (n : ℕ) :
    cofibrations C (latchingMap X n) :=
  (reedyModelCategory.isCofibrant_iff_latchingMapsIn X).mp inferInstance n

example (hX : ∀ n : ℕ, cofibrations C (latchingMap X n)) :
    IsCofibrant X :=
  (reedyModelCategory.isCofibrant_iff_latchingMapsIn X).mpr hX

example [IsCofibrant X] :
    cofibrations C (initial.to (X.obj (op ⦋0⦌))) := by
  have h₀ : cofibrations C (latchingMap X 0) :=
    (reedyModelCategory.isCofibrant_iff_latchingMapsIn X).mp inferInstance 0
  exact ((cofibrations C).arrow_mk_iso_iff
    (latchingMapZeroArrowIso X)).mp h₀

end CofibrantObjects

#synth IsWeakFactorizationSystem
  (trivialCofibrations (SimplicialObject C))
  (fibrations (SimplicialObject C))

#synth IsWeakFactorizationSystem
  (cofibrations (SimplicialObject C))
  (trivialFibrations (SimplicialObject C))

#synth ModelCategory (SimplicialObject (SimplicialObject C))

#guard_msgs (error, substring := true) in
#synth ModelCategory (Discrete WalkingPair ⥤ C)

section MixedUniverses

universe v' u'

variable {D : Type u'} [Category.{v'} D] [ModelCategory D]

#synth ModelCategory (SimplicialObject D)

example :
    weakEquivalences (SimplicialObject D) =
      (weakEquivalences D).functorCategory SimplexCategoryᵒᵖ :=
  rfl

example :
    cofibrations (SimplicialObject D) = reedyLeft (cofibrations D) :=
  rfl

example :
    fibrations (SimplicialObject D) = reedyRight (fibrations D) :=
  rfl

end MixedUniverses

#check @reedyModelCategory.isCofibrant_iff_latchingMapsIn.{0, 0}
#check @reedyModelCategory.isCofibrant_iff_latchingMapsIn.{1, 1}
#check @reedyModelCategory.isCofibrant_iff_latchingMapsIn.{0, 1}
#check @reedyModelCategory.isCofibrant_iff_latchingMapsIn.{1, 0}

end ScopeOn

section ScopeTeardown

variable {C : Type u} [Category.{v} C] [ModelCategory C]

#guard_msgs (error, substring := true) in
#synth ModelCategory (SimplicialObject C)

#guard_msgs (error, substring := true) in
#synth CategoryWithWeakEquivalences (SimplicialObject C)

#guard_msgs (error, substring := true) in
#synth CategoryWithCofibrations (SimplicialObject C)

#guard_msgs (error, substring := true) in
#synth CategoryWithFibrations (SimplicialObject C)

example (_X : SimplicialObject C) : True := by
  fail_if_success
    let _ : IsCofibrant _X := inferInstance
  trivial

end ScopeTeardown

section PrivateParents

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyModelCategory.instCategoryWithWeakEquivalences

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyModelCategory.instCategoryWithCofibrations

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyModelCategory.instCategoryWithFibrations

end PrivateParents

section Nonclaims

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyModelCategory.instIsLeftProper

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyModelCategory.instIsRightProper

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyModelCategory.instSimplicialCategory

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyModelCategory.localizedModelCategory

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.ReedyCofibrant

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyModelCategory.isCofibrant_iff_pointwise

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyModelCategory.isCofibrant_iff_proper

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyModelCategory.instIsCofibrantOfLatchingMapsIn

end Nonclaims

#print axioms CategoryTheory.SimplicialObject.reedyModelCategory
#print axioms CategoryTheory.SimplicialObject.reedyModelCategory.instModelCategory
#print axioms CategoryTheory.SimplicialObject.reedyModelCategory.isCofibrant_iff_latchingMapsIn

end CategoryTheory.SimplicialObject
