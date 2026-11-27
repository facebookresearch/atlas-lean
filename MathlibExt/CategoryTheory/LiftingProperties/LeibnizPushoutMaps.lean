/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.LiftingProperties.LeibnizMate

/-!
# Map legs of the canonical natural-transformation Leibniz pushout

The original chosen pushout and both source-square legs are retained by the
existing `NatTrans.leibnizPushout` functor.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uC vC uD vD

namespace CategoryTheory.NatTrans

open CategoryTheory Limits

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [HasPushouts C] {P Q : D ⥤ C} (α : P ⟶ Q)

/-- The canonical corner square retains the original target-functor map. -/
theorem leibnizPushout_map_right {g h : Arrow D} (f : g ⟶ h) :
    ((leibnizPushout α).map f).right = Q.map f.right := rfl

/-- The first original pushout projection retains the source square's left leg. -/
theorem leibnizPushout_map_left_inl {g h : Arrow D} (f : g ⟶ h) :
    pushout.inl (α.app g.left) (P.map g.hom) ≫ ((leibnizPushout α).map f).left =
      Q.map f.left ≫ pushout.inl (α.app h.left) (P.map h.hom) := by
  exact (Functor.PushoutObjObj.ofHasPushout (parallelPair α α)
    WalkingParallelPairHom.left g.hom).isPushout.inl_desc _ _ _

/-- The second original pushout projection retains the source square's right leg. -/
theorem leibnizPushout_map_left_inr {g h : Arrow D} (f : g ⟶ h) :
    pushout.inr (α.app g.left) (P.map g.hom) ≫ ((leibnizPushout α).map f).left =
      P.map f.right ≫ pushout.inr (α.app h.left) (P.map h.hom) := by
  exact (Functor.PushoutObjObj.ofHasPushout (parallelPair α α)
    WalkingParallelPairHom.left g.hom).isPushout.inr_desc _ _ _

end CategoryTheory.NatTrans
