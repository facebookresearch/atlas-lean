/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceLiftingComponents

/-!
# Tests for concrete join-slice transposition components
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet

example {K₀ K A B X Y : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (p : X ⟶ Y)
    (sq : Arrow.mk (joinUnderPushoutMap i a) ⟶
      Arrow.mk (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))) :
    (sliceUnder.restrictionArrowHomEquiv i a f p sq).left =
      (joinUnderAdjunction K).homEquiv A (Under.mk f)
        (joinUnderPushoutInl i a ≫ sq.left) :=
  sliceUnder.restrictionArrowHomEquiv_left i a f p sq

example {K₀ K A B X Y : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (p : X ⟶ Y)
    (sq : Arrow.mk (joinUnderPushoutMap i a) ⟶
      Arrow.mk (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))) :
    (sliceUnder.restrictionArrowHomEquiv i a f p sq).right ≫
        pullback.fst (sliceUnder.map X (i ≫ f) p)
          (sliceUnder.restrict Y (f ≫ p) i) =
      (joinUnderRestrictionAdjunction i).homEquiv B (Under.mk f)
        (joinUnderPushoutInr i a ≫ sq.left) :=
  sliceUnder.restrictionArrowHomEquiv_right_fst i a f p sq

example {K₀ K A B X Y : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (p : X ⟶ Y)
    (sq : Arrow.mk (joinUnderPushoutMap i a) ⟶
      Arrow.mk (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))) :
    (sliceUnder.restrictionArrowHomEquiv i a f p sq).right ≫
        pullback.snd (sliceUnder.map X (i ≫ f) p)
          (sliceUnder.restrict Y (f ≫ p) i) =
      (joinUnderAdjunction K).homEquiv B (Under.mk (f ≫ p)) sq.right :=
  sliceUnder.restrictionArrowHomEquiv_right_snd i a f p sq

example {K₀ K A B X Y : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (p : X ⟶ Y)
    (sq : Arrow.mk (joinUnderPushoutMap i a) ⟶
      Arrow.mk (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))) :
    (sliceUnder.restrictionArrowHomEquiv i a f p sq).right ≫
        pullback.fst (sliceUnder.map X (i ≫ f) p)
          (sliceUnder.restrict Y (f ≫ p) i) ≫
        sliceUnder.proj X (i ≫ f) =
      joinInr K₀ B ≫ (joinUnderPushoutObjObj i a).inr ≫ sq.left.right :=
  sliceUnder.restrictionArrowHomEquiv_right_fst_proj i a f p sq

end SSet
