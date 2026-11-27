/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeLatchingIso

/-!
# Tests for identity, degree-zero, and initial relative latching arrows
-/

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace MathlibExtTest.SimplicialObjectRelativeLatchingIso

variable (X : SimplicialObject (Type u)) (n : ℕ)

example :
    Arrow.mk (SimplicialObject.relativeLatchingMap (𝟙 X) n) ≅
      Arrow.mk (𝟙 (X.obj (op ⦋n⦌))) :=
  SimplicialObject.relativeLatchingMapIdArrowIso X n

example :
    (SimplicialObject.relativeLatchingMapIdArrowIso X n).hom.right = 𝟙 _ :=
  rfl


example :
    (SimplicialObject.relativeLatchingMapIdArrowIso X n).hom.left =
      inv (pushout.inl (SimplicialObject.latchingMap X n)
        ((SimplicialObject.latchingObjectFunctor n).map (𝟙 X))) :=
  rfl

example :
    (SimplicialObject.relativeLatchingMapIdArrowIso X n).inv.left =
      pushout.inl (SimplicialObject.latchingMap X n)
        ((SimplicialObject.latchingObjectFunctor n).map (𝟙 X)) :=
  rfl

variable {X Y : SimplicialObject (Type u)} (f : X ⟶ Y)

example :
    Arrow.mk (SimplicialObject.relativeLatchingMap f 0) ≅
      Arrow.mk (f.app (op ⦋0⦌)) :=
  SimplicialObject.relativeLatchingMapZeroArrowIso f

example :
    (SimplicialObject.relativeLatchingMapZeroArrowIso f).hom.right = 𝟙 _ :=
  rfl

example :
    (SimplicialObject.relativeLatchingMapZeroArrowIso f).inv.left =
      pushout.inl (SimplicialObject.latchingMap X 0)
        ((SimplicialObject.latchingObjectFunctor 0).map f) :=
  rfl

section InitialComparison

variable {C : Type u} [Category.{v} C]
variable [HasInitial C] [HasPushouts C]
variable (Z : SimplicialObject C) (m : ℕ)
variable [HasColimitsOfShape (SimplicialObject.latchingIndex m) C]

example :
    Arrow.mk (SimplicialObject.relativeLatchingMap (initial.to Z) m) ≅
      Arrow.mk (SimplicialObject.latchingMap Z m) :=
  SimplicialObject.relativeLatchingMapInitialArrowIso Z m

example :
    SimplicialObject.relativeLatchingObject (initial.to Z) m ⟶
      SimplicialObject.latchingObject Z m :=
  (SimplicialObject.relativeLatchingMapInitialArrowIso Z m).hom.left

example :
    (SimplicialObject.relativeLatchingMapInitialArrowIso Z m).inv.left =
      pushout.inr
        (SimplicialObject.latchingMap
          (⊥_ (SimplicialObject C)) m)
        ((SimplicialObject.latchingObjectFunctor m).map (initial.to Z)) :=
  rfl

example :
    (SimplicialObject.relativeLatchingMapInitialArrowIso Z m).hom.right =
      𝟙 _ :=
  rfl

example :
    (SimplicialObject.relativeLatchingMapInitialArrowIso Z m).hom.left ≫
        SimplicialObject.latchingMap Z m =
      SimplicialObject.relativeLatchingMap (initial.to Z) m ≫
        (SimplicialObject.relativeLatchingMapInitialArrowIso Z m).hom.right :=
  (SimplicialObject.relativeLatchingMapInitialArrowIso Z m).hom.w

end InitialComparison

section InitialComparisonZero

variable {C : Type u} [Category.{v} C]
variable [HasInitial C] [HasPushouts C]
variable (Z : SimplicialObject C)
variable [HasColimitsOfShape (SimplicialObject.latchingIndex 0) C]

example :
    Arrow.mk (SimplicialObject.relativeLatchingMap (initial.to Z) 0) ≅
      Arrow.mk (initial.to (Z.obj (op ⦋0⦌))) :=
  SimplicialObject.relativeLatchingMapInitialArrowIso Z 0 ≪≫
    SimplicialObject.latchingMapZeroArrowIso Z

end InitialComparisonZero

section IsIsoComparison

variable {C : Type u} [Category.{v} C]
variable {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ)
variable [HasColimitsOfShape (SimplicialObject.latchingIndex n) C]
variable [HasPushout (SimplicialObject.latchingMap X n)
  ((SimplicialObject.latchingObjectFunctor n).map f)]
variable [IsIso ((SimplicialObject.latchingObjectFunctor n).map f)]

example :
    Arrow.mk (SimplicialObject.relativeLatchingMap f n) ≅
      Arrow.mk (f.app (op ⦋n⦌)) :=
  SimplicialObject.relativeLatchingMapArrowIsoOfIsIso f n

example :
    (SimplicialObject.relativeLatchingMapArrowIsoOfIsIso f n).hom.left =
      inv (pushout.inl (SimplicialObject.latchingMap X n)
        ((SimplicialObject.latchingObjectFunctor n).map f)) :=
  rfl

example :
    (SimplicialObject.relativeLatchingMapArrowIsoOfIsIso f n).hom.right = 𝟙 _ :=
  rfl

example :
    (SimplicialObject.relativeLatchingMapArrowIsoOfIsIso f n).inv.left =
      pushout.inl (SimplicialObject.latchingMap X n)
        ((SimplicialObject.latchingObjectFunctor n).map f) :=
  rfl

end IsIsoComparison

#guard_msgs (error, substring := true) in
#check SimplicialObject.relativeLatchingMapArrowFunctor

#guard_msgs (error, substring := true) in
#check SimplicialObject.initialSimplicialObjectObjIsInitial
#guard_msgs (error, substring := true) in
#check SimplicialObject.initialLatchingCocone
#guard_msgs (error, substring := true) in
#check SimplicialObject.initialLatchingObjectIsInitial
#guard_msgs (error, substring := true) in
#check SimplicialObject.initialLatchingMapIsIso

#guard_msgs (error, substring := true) in
#check SimplicialObject.relativeLatchingMapInitialArrowIso_of_nonempty
#guard_msgs (error, substring := true) in
#check SimplicialObject.ReedyCofibrant
#guard_msgs (error, substring := true) in
#check SimplicialObject.isCofibrant_iff_latchingMapsIn

#check @SimplicialObject.relativeLatchingMapInitialArrowIso.{0, 0}
#check @SimplicialObject.relativeLatchingMapInitialArrowIso.{1, 1}
#check @SimplicialObject.relativeLatchingMapInitialArrowIso.{0, 1}
#check @SimplicialObject.relativeLatchingMapInitialArrowIso.{1, 0}

#print axioms SimplicialObject.relativeLatchingMapIdArrowIso
#print axioms SimplicialObject.relativeLatchingMapZeroArrowIso
#print axioms SimplicialObject.relativeLatchingMapInitialArrowIso

end MathlibExtTest.SimplicialObjectRelativeLatchingIso
