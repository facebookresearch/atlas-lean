/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHorn

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

variable (p q : ℕ) (j : Fin (q + 2)) (i : Fin (p + 2))

example : (rightJoinHornIndex p q j).val = p + 1 + j.val := by simp

example : (leftJoinHornIndex p q i).val = i.val := by simp

example :
    (joinBoundaryHornRightPushoutObjObj.{u} p q j).inl ≫
        (joinBoundaryHornRightArrowIso p q j).hom.left =
      joinBoundaryHornRightFactorMap p q j :=
  joinBoundaryHornRightArrowIso_hom_inl p q j

example :
    (joinBoundaryHornRightPushoutObjObj.{u} p q j).inr ≫
        (joinBoundaryHornRightArrowIso p q j).hom.left =
      joinBoundaryHornRightBoundaryFactorMap p q j :=
  joinBoundaryHornRightArrowIso_hom_inr p q j

example :
    (joinHornBoundaryLeftPushoutObjObj.{u} p q i).inl ≫
        (joinHornBoundaryLeftArrowIso p q i).hom.left =
      joinHornBoundaryLeftBoundaryFactorMap p q i :=
  joinHornBoundaryLeftArrowIso_hom_inl p q i

example :
    (joinHornBoundaryLeftPushoutObjObj.{u} p q i).inr ≫
        (joinHornBoundaryLeftArrowIso p q i).hom.left =
      joinHornBoundaryLeftHornFactorMap p q i :=
  joinHornBoundaryLeftArrowIso_hom_inr p q i

example :
    (joinBoundaryHornRightArrowIso.{u} p q j).hom.left ≫
        (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j)).ι =
      (joinBoundaryHornRightPushoutObjObj p q j).ι ≫
        (joinStdSimplexIso p (q + 1)).hom :=
  joinBoundaryHornRightArrowIso_hom_w p q j

example :
    (joinHornBoundaryLeftArrowIso.{u} p q i).hom.left ≫
        (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i)).ι =
      (joinHornBoundaryLeftPushoutObjObj p q i).ι ≫
        (joinStdSimplexIso (p + 1) q).hom :=
  joinHornBoundaryLeftArrowIso_hom_w p q i

example : Mono (joinBoundaryHornRightPushoutObjObj.{u} p q j).ι := inferInstance

example : Mono (joinHornBoundaryLeftPushoutObjObj.{u} p q i).ι := inferInstance

example (q : ℕ) (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).inr ≫
        (joinBoundaryHornRightPointIso 0 q j).hom =
      joinBoundaryHornRightBoundaryFactorMap 0 q j :=
  joinBoundaryHornRightPointIso_hom_inr 0 q j

example (p : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).inl ≫
        (joinHornBoundaryLeftPointIso p 0 i).hom =
      joinHornBoundaryLeftBoundaryFactorMap p 0 i :=
  joinHornBoundaryLeftPointIso_hom_inl p 0 i

end SSet
