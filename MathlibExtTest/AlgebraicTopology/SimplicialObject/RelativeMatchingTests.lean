/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeMatching

/-!
# Tests for relative matching maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace MathlibExtTest.SimplicialObjectRelativeMatching

variable {X Y : SimplicialObject (Type u)} (f : X ⟶ Y) (n : ℕ)

example : Type u :=
  SimplicialObject.relativeMatchingObject f n

example : X.obj (op ⦋n⦌) ⟶
    SimplicialObject.relativeMatchingObject f n :=
  SimplicialObject.relativeMatchingMap f n

example :
    SimplicialObject.relativeMatchingMap f n ≫
        pullback.fst (SimplicialObject.matchingMap Y n)
          ((SimplicialObject.matchingObjectFunctor n).map f) =
      f.app (op ⦋n⦌) :=
  SimplicialObject.relativeMatchingMap_fst f n

example :
    SimplicialObject.relativeMatchingMap f n ≫
        pullback.snd (SimplicialObject.matchingMap Y n)
          ((SimplicialObject.matchingObjectFunctor n).map f) =
      SimplicialObject.matchingMap X n :=
  SimplicialObject.relativeMatchingMap_snd f n

example : X.obj (op ⦋1⦌) ⟶
    SimplicialObject.relativeMatchingObject f 1 :=
  SimplicialObject.relativeMatchingMap f 1

#check SimplicialObject.relativeMatchingObject
#check SimplicialObject.relativeMatchingMap
#check SimplicialObject.relativeMatchingMap_fst
#check SimplicialObject.relativeMatchingMap_snd

#guard_msgs (error, substring := true) in
#check SimplicialObject.relativeMatchingMapReversed
#guard_msgs (error, substring := true) in
#check SimplicialObject.relativeMatchingMapZeroArrowIso
#guard_msgs (error, substring := true) in
#check SimplicialObject.relativeMatchingMapArrowFunctor

#print axioms SimplicialObject.relativeMatchingObject
#print axioms SimplicialObject.relativeMatchingMap
#print axioms SimplicialObject.relativeMatchingMap_fst
#print axioms SimplicialObject.relativeMatchingMap_snd

end MathlibExtTest.SimplicialObjectRelativeMatching
