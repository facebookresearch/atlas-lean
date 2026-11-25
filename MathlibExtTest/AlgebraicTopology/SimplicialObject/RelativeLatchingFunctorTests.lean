/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeLatchingFunctor

/-!
# Tests for functorial relative latching arrows
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace MathlibExtTest.SimplicialObjectRelativeLatchingFunctor

section PointwiseAssumptions

variable {D : Type u} [Category D] [HasPushouts D]
variable (k : ℕ) [HasColimitsOfShape (SimplicialObject.latchingIndex k) D]

example : Arrow (SimplicialObject D) ⥤ Arrow D :=
  SimplicialObject.relativeLatchingMapArrowFunctor k

end PointwiseAssumptions

variable (n : ℕ)
variable {f g h : Arrow (SimplicialObject (Type u))}

example : Arrow (SimplicialObject (Type u)) ⥤ Arrow (Type u) :=
  SimplicialObject.relativeLatchingMapArrowFunctor n

example (f : Arrow (SimplicialObject (Type u))) :
    (SimplicialObject.relativeLatchingMapArrowFunctor n).obj f =
      Arrow.mk (SimplicialObject.relativeLatchingMap f.hom n) :=
  rfl

example (q : f ⟶ g) :
    ((SimplicialObject.relativeLatchingMapArrowFunctor n).map q).right =
      q.right.app (op ⦋n⦌) :=
  rfl

example (q : f ⟶ g) :
    pushout.inl (SimplicialObject.latchingMap f.left n)
          ((SimplicialObject.latchingObjectFunctor n).map f.hom) ≫
        ((SimplicialObject.relativeLatchingMapArrowFunctor n).map q).left =
      q.left.app (op ⦋n⦌) ≫
        pushout.inl (SimplicialObject.latchingMap g.left n)
          ((SimplicialObject.latchingObjectFunctor n).map g.hom) :=
  SimplicialObject.relativeLatchingMapArrowFunctor_map_left_inl n q

example (q : f ⟶ g) :
    pushout.inr (SimplicialObject.latchingMap f.left n)
          ((SimplicialObject.latchingObjectFunctor n).map f.hom) ≫
        ((SimplicialObject.relativeLatchingMapArrowFunctor n).map q).left =
      (SimplicialObject.latchingObjectFunctor n).map q.right ≫
        pushout.inr (SimplicialObject.latchingMap g.left n)
          ((SimplicialObject.latchingObjectFunctor n).map g.hom) :=
  SimplicialObject.relativeLatchingMapArrowFunctor_map_left_inr n q

example (q : f ⟶ g) :
    ((SimplicialObject.relativeLatchingMapArrowFunctor n).map q).left ≫
        SimplicialObject.relativeLatchingMap g.hom n =
      SimplicialObject.relativeLatchingMap f.hom n ≫
        ((SimplicialObject.relativeLatchingMapArrowFunctor n).map q).right :=
  Arrow.w ((SimplicialObject.relativeLatchingMapArrowFunctor n).map q)

example (f : Arrow (SimplicialObject (Type u))) :
    (SimplicialObject.relativeLatchingMapArrowFunctor n).map (𝟙 f) =
      𝟙 ((SimplicialObject.relativeLatchingMapArrowFunctor n).obj f) :=
  (SimplicialObject.relativeLatchingMapArrowFunctor n).map_id f

example (q : f ⟶ g) (r : g ⟶ h) :
    (SimplicialObject.relativeLatchingMapArrowFunctor n).map (q ≫ r) =
      (SimplicialObject.relativeLatchingMapArrowFunctor n).map q ≫
        (SimplicialObject.relativeLatchingMapArrowFunctor n).map r :=
  (SimplicialObject.relativeLatchingMapArrowFunctor n).map_comp q r

example {f g : Arrow (SimplicialObject (Type u))} (e : f ≅ g) :
    (SimplicialObject.relativeLatchingMapArrowFunctor n).obj f ≅
      (SimplicialObject.relativeLatchingMapArrowFunctor n).obj g :=
  (SimplicialObject.relativeLatchingMapArrowFunctor n).mapIso e

#guard_msgs (error, substring := true) in
#check SimplicialObject.relativeLatchingObjectMap
#guard_msgs (error, substring := true) in
#check SimplicialObject.relativeLatchingMapArrowFunctorMap
#guard_msgs (error, substring := true) in
#check SimplicialObject.ReedyCofibration

#print axioms SimplicialObject.relativeLatchingMapArrowFunctor
#print axioms SimplicialObject.relativeLatchingMapArrowFunctor_obj
#print axioms SimplicialObject.relativeLatchingMapArrowFunctor_map_right
#print axioms SimplicialObject.relativeLatchingMapArrowFunctor_map_left_inl
#print axioms SimplicialObject.relativeLatchingMapArrowFunctor_map_left_inr

end MathlibExtTest.SimplicialObjectRelativeLatchingFunctor
