/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeMatchingIso

/-!
# Tests for identity and degree-zero relative matching arrows
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace MathlibExtTest.SimplicialObjectRelativeMatchingIso

variable (X : SimplicialObject (Type u)) (n : ℕ)

example :
    Arrow.mk (SimplicialObject.relativeMatchingMap (𝟙 X) n) ≅
      Arrow.mk (𝟙 (X.obj (op ⦋n⦌))) :=
  SimplicialObject.relativeMatchingMapIdArrowIso X n

example :
    (SimplicialObject.relativeMatchingMapIdArrowIso X n).hom.left = 𝟙 _ :=
  rfl

example :
    (SimplicialObject.relativeMatchingMapIdArrowIso X n).hom.right =
      pullback.fst (SimplicialObject.matchingMap X n)
        ((SimplicialObject.matchingObjectFunctor n).map (𝟙 X)) :=
  rfl

variable {X Y : SimplicialObject (Type u)} (f : X ⟶ Y)

example :
    Arrow.mk (SimplicialObject.relativeMatchingMap f 0) ≅
      Arrow.mk (f.app (op ⦋0⦌)) :=
  SimplicialObject.relativeMatchingMapZeroArrowIso f

example :
    (SimplicialObject.relativeMatchingMapZeroArrowIso f).hom.left = 𝟙 _ :=
  rfl

example :
    (SimplicialObject.relativeMatchingMapZeroArrowIso f).hom.right =
      pullback.fst (SimplicialObject.matchingMap Y 0)
        ((SimplicialObject.matchingObjectFunctor 0).map f) :=
  rfl

#guard_msgs (error, substring := true) in
#check SimplicialObject.relativeMatchingMapArrowFunctor

#print axioms SimplicialObject.relativeMatchingMapIdArrowIso
#print axioms SimplicialObject.relativeMatchingMapZeroArrowIso

end MathlibExtTest.SimplicialObjectRelativeMatchingIso
