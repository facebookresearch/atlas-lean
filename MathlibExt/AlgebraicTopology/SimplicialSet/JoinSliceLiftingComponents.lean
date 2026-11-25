/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceLifting

/-!
# Components of the concrete join-slice transposition

This file exposes the three components of Joyal's concrete Lemma 3.14 square
bijection in the under-slice orientation.  The final projection formula
identifies the transposed interval edge used in the relative extension
argument.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
## Components of the concrete under-slice transposition
-/

/-- The left component of the concrete transposed under-slice square. -/
theorem sliceUnder.restrictionArrowHomEquiv_left
    {K₀ K A B X Y : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (p : X ⟶ Y)
    (sq : Arrow.mk (joinUnderPushoutMap i a) ⟶
      Arrow.mk (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))) :
    (sliceUnder.restrictionArrowHomEquiv i a f p sq).left =
      (joinUnderAdjunction K).homEquiv A (Under.mk f)
        (joinUnderPushoutInl i a ≫ sq.left) := by
  simp only [Arrow.mk_left, restrictionArrowHomEquiv_apply,
    Arrow.comp_left]
  exact Adjunction.leibnizMateArrowHomEquivOf_apply_left
    (joinUnderRestrictionAdjunction i) (joinUnderAdjunction K)
    (joinUnderRestrictionNatTrans i) a
    (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))
    (joinUnderMatePushoutObjObj i a)
    (sliceUnder.restrictionPullbackObjObjOfHom i
      (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))) sq

/-- The first concrete pullback component of the transposed under-slice
square. -/
theorem sliceUnder.restrictionArrowHomEquiv_right_fst
    {K₀ K A B X Y : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (p : X ⟶ Y)
    (sq : Arrow.mk (joinUnderPushoutMap i a) ⟶
      Arrow.mk (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))) :
    (sliceUnder.restrictionArrowHomEquiv i a f p sq).right ≫
        pullback.fst (sliceUnder.map X (i ≫ f) p)
          (sliceUnder.restrict Y (f ≫ p) i) =
      (joinUnderRestrictionAdjunction i).homEquiv B (Under.mk f)
        (joinUnderPushoutInr i a ≫ sq.left) := by
  simp only [Arrow.mk_right, restrictionArrowHomEquiv_apply,
    Arrow.comp_right, Category.assoc, Functor.comp_obj]
  change
    (sliceUnder.restrictionArrowHomEquivOfHom i a
      (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p)) sq).right ≫
        (sliceUnder.restrictionConcretePullbackIso i f p).hom ≫
        pullback.fst (sliceUnder.map X (i ≫ f) p)
          (sliceUnder.restrict Y (f ≫ p) i) = _
  calc
    _ =
        (sliceUnder.restrictionArrowHomEquivOfHom i a
          (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p)) sq).right ≫
          pullback.fst
            ((joinLeftDivision K₀).map ((Under.map i).map
              (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))))
            ((joinUnderMateBeta i).app (Under.mk (f ≫ p))) := by
      simpa only [Category.assoc] using congrArg
        (fun z =>
          (sliceUnder.restrictionArrowHomEquivOfHom i a
            (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p)) sq).right ≫ z)
        (sliceUnder.restrictionConcretePullbackIso_hom_fst i f p)
    _ = _ := by
      exact Adjunction.leibnizMateArrowHomEquivOf_apply_right_fst
        (joinUnderRestrictionAdjunction i) (joinUnderAdjunction K)
        (joinUnderRestrictionNatTrans i) a
        (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))
        (joinUnderMatePushoutObjObj i a)
        (sliceUnder.restrictionPullbackObjObjOfHom i
          (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))) sq

/-- The second concrete pullback component of the transposed under-slice
square. -/
theorem sliceUnder.restrictionArrowHomEquiv_right_snd
    {K₀ K A B X Y : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (p : X ⟶ Y)
    (sq : Arrow.mk (joinUnderPushoutMap i a) ⟶
      Arrow.mk (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))) :
    (sliceUnder.restrictionArrowHomEquiv i a f p sq).right ≫
        pullback.snd (sliceUnder.map X (i ≫ f) p)
          (sliceUnder.restrict Y (f ≫ p) i) =
      (joinUnderAdjunction K).homEquiv B (Under.mk (f ≫ p)) sq.right := by
  simp only [Arrow.mk_right, restrictionArrowHomEquiv_apply,
    Arrow.comp_right, Category.assoc]
  change
    (sliceUnder.restrictionArrowHomEquivOfHom i a
      (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p)) sq).right ≫
        (sliceUnder.restrictionConcretePullbackIso i f p).hom ≫
        pullback.snd (sliceUnder.map X (i ≫ f) p)
          (sliceUnder.restrict Y (f ≫ p) i) = _
  calc
    _ =
        (sliceUnder.restrictionArrowHomEquivOfHom i a
          (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p)) sq).right ≫
          pullback.snd
            ((joinLeftDivision K₀).map ((Under.map i).map
              (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))))
            ((joinUnderMateBeta i).app (Under.mk (f ≫ p))) := by
      simpa only [Category.assoc] using congrArg
        (fun z =>
          (sliceUnder.restrictionArrowHomEquivOfHom i a
            (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p)) sq).right ≫ z)
        (sliceUnder.restrictionConcretePullbackIso_hom_snd i f p)
    _ = _ := by
      exact Adjunction.leibnizMateArrowHomEquivOf_apply_right_snd
        (joinUnderRestrictionAdjunction i) (joinUnderAdjunction K)
        (joinUnderRestrictionNatTrans i) a
        (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))
        (joinUnderMatePushoutObjObj i a)
        (sliceUnder.restrictionPullbackObjObjOfHom i
          (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))) sq

/-- The slice projection of a classified map is restriction of its whole join
map to the free right factor. -/
lemma sliceUnder.comp_proj_eq_joinInr_comp_homEquiv
    {K B X : SSet.{u}} (f : K ⟶ X) (φ : B ⟶ sliceUnder X f) :
    φ ≫ sliceUnder.proj X f =
      joinInr K B ≫ (sliceUnder.homEquiv X f B φ).1 := by
  rw [sliceUnder.homEquiv_apply]
  dsimp only
  rw [← Category.assoc, ← map_comp_joinInr, Category.assoc,
    sliceUnder.joinInr_evaluation]

/-- After the first pullback projection and the slice projection, the
transposed component is the original top map on the free right factor. -/
theorem sliceUnder.restrictionArrowHomEquiv_right_fst_proj
    {K₀ K A B X Y : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (p : X ⟶ Y)
    (sq : Arrow.mk (joinUnderPushoutMap i a) ⟶
      Arrow.mk (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p))) :
    (sliceUnder.restrictionArrowHomEquiv i a f p sq).right ≫
        pullback.fst (sliceUnder.map X (i ≫ f) p)
          (sliceUnder.restrict Y (f ≫ p) i) ≫
        sliceUnder.proj X (i ≫ f) =
      joinInr K₀ B ≫ (joinUnderPushoutObjObj i a).inr ≫ sq.left.right := by
  calc
    _ = (joinUnderRestrictionAdjunction i).homEquiv B (Under.mk f)
          (joinUnderPushoutInr i a ≫ sq.left) ≫
          sliceUnder.proj X (i ≫ f) := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ sliceUnder.proj X (i ≫ f))
        (sliceUnder.restrictionArrowHomEquiv_right_fst i a f p sq)
    _ = _ := by
      let φ : B ⟶ sliceUnder X (i ≫ f) :=
        (joinUnderRestrictionAdjunction i).homEquiv B (Under.mk f)
          (joinUnderPushoutInr i a ≫ sq.left)
      change φ ≫ sliceUnder.proj X (i ≫ f) = _
      rw [sliceUnder.comp_proj_eq_joinInr_comp_homEquiv]
      dsimp only [φ]
      rw [joinUnderRestrictionAdjunction, Adjunction.comp_homEquiv,
        joinUnderAdjunction]
      simp only [Functor.comp_obj, Under.pushout_obj, joinUnder_obj_hom,
        Adjunction.mkOfHomEquiv_homEquiv, Equiv.trans_apply,
        joinUnderHomEquiv_apply, Under.map_obj_right, Under.mk_right,
        Under.map_obj_hom, Under.mk_hom, Arrow.mk_left,
        Equiv.apply_symm_apply]
      change joinInr K₀ B ≫
          pushout.inl (joinInl K₀ B) i ≫
            (joinUnderPushoutInr i a ≫ sq.left).right = _
      simp only [joinUnderPushoutInr, Under.homMk_right,
        Under.comp_right]
      have hdesc : pushout.inl (joinInl K₀ B) i ≫
          joinUnderPushoutDesc i a =
            (joinUnderPushoutObjObj i a).inr :=
        pushout.inl_desc _ _ _
      simp only [← Category.assoc, hdesc]

end SSet
