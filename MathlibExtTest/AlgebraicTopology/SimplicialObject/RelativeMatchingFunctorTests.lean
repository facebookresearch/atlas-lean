/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeMatchingFunctor

/-!
# Tests for functorial relative matching arrows
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace MathlibExtTest.SimplicialObjectRelativeMatchingFunctor

section PointwiseAssumptions

variable {D : Type u} [Category D] [HasPullbacks D]
variable (k : ℕ) [HasLimitsOfShape (SimplicialObject.matchingIndex k) D]

example : Arrow (SimplicialObject D) ⥤ Arrow D :=
  SimplicialObject.relativeMatchingMapArrowFunctor k

end PointwiseAssumptions

variable (n : ℕ)
variable {f g h : Arrow (SimplicialObject (Type u))}

example : Arrow (SimplicialObject (Type u)) ⥤ Arrow (Type u) :=
  SimplicialObject.relativeMatchingMapArrowFunctor n

example (f : Arrow (SimplicialObject (Type u))) :
    (SimplicialObject.relativeMatchingMapArrowFunctor n).obj f =
      Arrow.mk (SimplicialObject.relativeMatchingMap f.hom n) :=
  rfl

example (q : f ⟶ g) :
    ((SimplicialObject.relativeMatchingMapArrowFunctor n).map q).left =
      q.left.app (op ⦋n⦌) :=
  rfl

example (q : f ⟶ g) :
    ((SimplicialObject.relativeMatchingMapArrowFunctor n).map q).right ≫
        pullback.fst (SimplicialObject.matchingMap g.right n)
          ((SimplicialObject.matchingObjectFunctor n).map g.hom) =
      pullback.fst (SimplicialObject.matchingMap f.right n)
          ((SimplicialObject.matchingObjectFunctor n).map f.hom) ≫
        q.right.app (op ⦋n⦌) :=
  SimplicialObject.relativeMatchingMapArrowFunctor_map_right_fst n q

example (q : f ⟶ g) :
    ((SimplicialObject.relativeMatchingMapArrowFunctor n).map q).right ≫
        pullback.snd (SimplicialObject.matchingMap g.right n)
          ((SimplicialObject.matchingObjectFunctor n).map g.hom) =
      pullback.snd (SimplicialObject.matchingMap f.right n)
          ((SimplicialObject.matchingObjectFunctor n).map f.hom) ≫
        (SimplicialObject.matchingObjectFunctor n).map q.left :=
  SimplicialObject.relativeMatchingMapArrowFunctor_map_right_snd n q

example (q : f ⟶ g) :
    ((SimplicialObject.relativeMatchingMapArrowFunctor n).map q).left ≫
        SimplicialObject.relativeMatchingMap g.hom n =
      SimplicialObject.relativeMatchingMap f.hom n ≫
        ((SimplicialObject.relativeMatchingMapArrowFunctor n).map q).right :=
  Arrow.w ((SimplicialObject.relativeMatchingMapArrowFunctor n).map q)

example (f : Arrow (SimplicialObject (Type u))) :
    (SimplicialObject.relativeMatchingMapArrowFunctor n).map (𝟙 f) = 𝟙 _ := by
  simp

example (q : f ⟶ g) (r : g ⟶ h) :
    (SimplicialObject.relativeMatchingMapArrowFunctor n).map (q ≫ r) =
      (SimplicialObject.relativeMatchingMapArrowFunctor n).map q ≫
        (SimplicialObject.relativeMatchingMapArrowFunctor n).map r := by
  simp

example {f g : Arrow (SimplicialObject (Type u))} (e : f ≅ g) :
    (SimplicialObject.relativeMatchingMapArrowFunctor n).obj f ≅
      (SimplicialObject.relativeMatchingMapArrowFunctor n).obj g :=
  (SimplicialObject.relativeMatchingMapArrowFunctor n).mapIso e

-- The four no-expose implementation declarations are pinned as an internal ledger.
#check SimplicialObject.relativeMatchingObjectMap
#check SimplicialObject.relativeMatchingObjectMap_fst
#check SimplicialObject.relativeMatchingObjectMap_snd
#check SimplicialObject.relativeMatchingMapArrowFunctor_w
#guard_msgs (error, substring := true) in
#check SimplicialObject.ReedyFibration

#print axioms SimplicialObject.relativeMatchingMapArrowFunctor
#print axioms SimplicialObject.relativeMatchingMapArrowFunctor_obj
#print axioms SimplicialObject.relativeMatchingMapArrowFunctor_map_left
#print axioms SimplicialObject.relativeMatchingMapArrowFunctor_map_right_fst
#print axioms SimplicialObject.relativeMatchingMapArrowFunctor_map_right_snd

end MathlibExtTest.SimplicialObjectRelativeMatchingFunctor
