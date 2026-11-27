/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyTrivialClasses

/-!
# Tests for trivial Reedy morphism classes
-/

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open HomotopicalAlgebra
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

section Equalities

variable {C : Type u} [Category.{v} C] [ModelCategory C]

example :
    reedyLeft (trivialCofibrations C) =
      reedyLeft (cofibrations C) ⊓
        (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ :=
  reedyLeft_trivialCofibrations_eq

example :
    reedyLeft (cofibrations C) ⊓
        (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ =
      reedyLeft (trivialCofibrations C) :=
  reedyLeft_trivialCofibrations_eq.symm

example :
    reedyRight (trivialFibrations C) =
      reedyRight (fibrations C) ⊓
        (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ :=
  reedyRight_trivialFibrations_eq

example :
    reedyRight (fibrations C) ⊓
        (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ =
      reedyRight (trivialFibrations C) :=
  reedyRight_trivialFibrations_eq.symm

end Equalities

section ArbitraryMaps

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable {X Y : SimplicialObject C} (f : X ⟶ Y)

example (h : reedyLeft (trivialCofibrations C) f) :
    reedyLeft (cofibrations C) f ∧
      (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ f := by
  rw [reedyLeft_trivialCofibrations_eq] at h
  exact h

example (hcof : reedyLeft (cofibrations C) f)
    (hweak : (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ f) :
    reedyLeft (trivialCofibrations C) f := by
  rw [reedyLeft_trivialCofibrations_eq]
  exact ⟨hcof, hweak⟩

example (h : reedyRight (trivialFibrations C) f) :
    reedyRight (fibrations C) f ∧
      (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ f := by
  rw [reedyRight_trivialFibrations_eq] at h
  exact h

example (hfib : reedyRight (fibrations C) f)
    (hweak : (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ f) :
    reedyRight (trivialFibrations C) f := by
  rw [reedyRight_trivialFibrations_eq]
  exact ⟨hfib, hweak⟩

end ArbitraryMaps

section DegreeZero

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable {X Y : SimplicialObject C} (f : X ⟶ Y)

example (hcof : reedyLeft (cofibrations C) f)
    (hweak : (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ f) :
    trivialCofibrations C (relativeLatchingMap f 0) := by
  have h : reedyLeft (trivialCofibrations C) f := by
    rw [reedyLeft_trivialCofibrations_eq]
    exact ⟨hcof, hweak⟩
  exact h 0

example (hfib : reedyRight (fibrations C) f)
    (hweak : (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ f) :
    trivialFibrations C (relativeMatchingMap f 0) := by
  have h : reedyRight (trivialFibrations C) f := by
    rw [reedyRight_trivialFibrations_eq]
    exact ⟨hfib, hweak⟩
  exact h 0

end DegreeZero

section MixedUniverses

universe v' u'

variable {D : Type u'} [Category.{v'} D] [ModelCategory D]

example :
    reedyLeft (trivialCofibrations D) =
      reedyLeft (cofibrations D) ⊓
        (weakEquivalences D).functorCategory SimplexCategoryᵒᵖ :=
  reedyLeft_trivialCofibrations_eq

example :
    reedyRight (trivialFibrations D) =
      reedyRight (fibrations D) ⊓
        (weakEquivalences D).functorCategory SimplexCategoryᵒᵖ :=
  reedyRight_trivialFibrations_eq

end MixedUniverses

section PrivateHelpers

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.ReedyTrivialClassesLatching.latchingIndexBelow

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.ReedyTrivialClassesLatching.filteredLatchingMap

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.ReedyTrivialClassesMatching.matchingIndexBelow

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.ReedyTrivialClassesMatching.filteredMatchingMap

end PrivateHelpers

section Nonclaims

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyTrivialModelCategory

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyProperModelCategory

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyLeftProper

#guard_msgs (error, substring := true) in
#check CategoryTheory.SimplicialObject.reedyRightProper

end Nonclaims

#print axioms CategoryTheory.SimplicialObject.reedyLeft_trivialCofibrations_eq
#print axioms CategoryTheory.SimplicialObject.reedyRight_trivialFibrations_eq

end CategoryTheory.SimplicialObject
