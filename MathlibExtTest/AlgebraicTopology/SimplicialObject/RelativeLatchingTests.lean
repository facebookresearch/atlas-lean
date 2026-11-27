/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeLatching

/-!
# Tests for relative latching maps
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace MathlibExtTest.SimplicialObjectRelativeLatching

variable {X Y : SimplicialObject (Type u)} (f : X ⟶ Y) (n : ℕ)

example : Type u :=
  SimplicialObject.relativeLatchingObject f n

example : SimplicialObject.relativeLatchingObject f n ⟶
    Y.obj (op ⦋n⦌) :=
  SimplicialObject.relativeLatchingMap f n

example :
    pushout.inl (SimplicialObject.latchingMap X n)
          ((SimplicialObject.latchingObjectFunctor n).map f) ≫
        SimplicialObject.relativeLatchingMap f n =
      f.app (op ⦋n⦌) :=
  SimplicialObject.relativeLatchingMap_inl f n

example :
    pushout.inr (SimplicialObject.latchingMap X n)
          ((SimplicialObject.latchingObjectFunctor n).map f) ≫
        SimplicialObject.relativeLatchingMap f n =
      SimplicialObject.latchingMap Y n :=
  SimplicialObject.relativeLatchingMap_inr f n

example : SimplicialObject.relativeLatchingObject f 1 ⟶
    Y.obj (op ⦋1⦌) :=
  SimplicialObject.relativeLatchingMap f 1

#check SimplicialObject.relativeLatchingObject
#check SimplicialObject.relativeLatchingMap
#check SimplicialObject.relativeLatchingMap_inl
#check SimplicialObject.relativeLatchingMap_inr

#guard_msgs (error, substring := true) in
#check SimplicialObject.relativeLatchingMapReversed
#guard_msgs (error, substring := true) in
#check SimplicialObject.relativeLatchingMapZeroArrowIso
#guard_msgs (error, substring := true) in
#check SimplicialObject.relativeLatchingMapArrowFunctor

#print axioms SimplicialObject.relativeLatchingObject
#print axioms SimplicialObject.relativeLatchingMap
#print axioms SimplicialObject.relativeLatchingMap_inl
#print axioms SimplicialObject.relativeLatchingMap_inr

end MathlibExtTest.SimplicialObjectRelativeLatching
