/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialSkeletalFiltration
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Finite latching pushouts and comparison arrows

The actual finite latching pushout and its original natural map.

These constructions identify the native chosen pushout map with the SAME
finite latching-stage map. They do not assume or prove stage sharpness,
an incoming HC comparison, a diagonal comparison, or a completion outcome.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.RezkFiniteLatchingPushout

/-- The literal map of the two original source-overlap spans. -/
def chosenMap {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    pushout ((outerLatchingStageBefore X n r).fromPreimage (X.σ r))
        (outerLatchingStageSourceOverlap X n r).ι ⟶
      pushout ((outerLatchingStageBefore Y n r).fromPreimage (Y.σ r))
        (outerLatchingStageSourceOverlap Y n r).ι :=
  pushout.map
    ((outerLatchingStageBefore X n r).fromPreimage (X.σ r))
    (outerLatchingStageSourceOverlap X n r).ι
    ((outerLatchingStageBefore Y n r).fromPreimage (Y.σ r))
    (outerLatchingStageSourceOverlap Y n r).ι
    (outerLatchingStageBeforeMap eta n r) (eta.app (op ⦋n⦌))
    (outerLatchingStageSourceOverlapMap eta n r)
    (outerLatchingStageSource_top_naturality eta n r).symm
    (outerLatchingStageSource_left_naturality eta n r).symm

/-- The chosen map restricts to the original preceding-stage map on the first leg. -/
theorem chosenMap_inl {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    pushout.inl ((outerLatchingStageBefore X n r).fromPreimage (X.σ r))
        (outerLatchingStageSourceOverlap X n r).ι ≫ chosenMap eta n r =
      outerLatchingStageBeforeMap eta n r ≫
        pushout.inl ((outerLatchingStageBefore Y n r).fromPreimage (Y.σ r))
          (outerLatchingStageSourceOverlap Y n r).ι := by
  simp only [chosenMap, pushout.map, pushout.inl_desc]

/-- The chosen map restricts to the original row map on the second leg. -/
theorem chosenMap_inr {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    pushout.inr ((outerLatchingStageBefore X n r).fromPreimage (X.σ r))
        (outerLatchingStageSourceOverlap X n r).ι ≫ chosenMap eta n r =
      eta.app (op ⦋n⦌) ≫
        pushout.inr ((outerLatchingStageBefore Y n r).fromPreimage (Y.σ r))
          (outerLatchingStageSourceOverlap Y n r).ι := by
  simp only [chosenMap, pushout.map, pushout.inr_desc]

/-- The native pushout inverses transport the chosen map to the actual stage map. -/
theorem chosenMap_stage_transport
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    (outerLatchingStageSource_isPushout X n r).isoPushout.inv ≫
        outerLatchingStageMap eta n r =
      chosenMap eta n r ≫
        (outerLatchingStageSource_isPushout Y n r).isoPushout.inv := by
  apply pushout.hom_ext
  · calc
      pushout.inl _ _ ≫
          ((outerLatchingStageSource_isPushout X n r).isoPushout.inv ≫
            outerLatchingStageMap eta n r) =
        (Subcomplex.homOfLE (by
          rw [outerLatchingStage_eq_before_sup_range]
          exact le_sup_left) :
          (outerLatchingStageBefore X n r : SSet.{u}) ⟶
            outerLatchingStage X n r) ≫ outerLatchingStageMap eta n r := by
          rw [← Category.assoc,
            (outerLatchingStageSource_isPushout X n r).inl_isoPushout_inv]
      _ = outerLatchingStageBeforeMap eta n r ≫
          (Subcomplex.homOfLE (by
            rw [outerLatchingStage_eq_before_sup_range]
            exact le_sup_left) :
            (outerLatchingStageBefore Y n r : SSet.{u}) ⟶
              outerLatchingStage Y n r) :=
          (outerLatchingStageSource_right_naturality eta n r).symm
      _ = pushout.inl _ _ ≫
          (chosenMap eta n r ≫
            (outerLatchingStageSource_isPushout Y n r).isoPushout.inv) := by
          symm
          rw [← Category.assoc, chosenMap_inl, Category.assoc,
            (outerLatchingStageSource_isPushout Y n r).inl_isoPushout_inv]
  · calc
      pushout.inr _ _ ≫
          ((outerLatchingStageSource_isPushout X n r).isoPushout.inv ≫
            outerLatchingStageMap eta n r) =
        outerDegeneracyToLatchingStage X n r ≫ outerLatchingStageMap eta n r := by
          rw [← Category.assoc,
            (outerLatchingStageSource_isPushout X n r).inr_isoPushout_inv]
      _ = eta.app (op ⦋n⦌) ≫ outerDegeneracyToLatchingStage Y n r :=
          (outerLatchingStageSource_bottom_naturality eta n r).symm
      _ = pushout.inr _ _ ≫
          (chosenMap eta n r ≫
            (outerLatchingStageSource_isPushout Y n r).isoPushout.inv) := by
          symm
          rw [← Category.assoc, chosenMap_inr, Category.assoc,
            (outerLatchingStageSource_isPushout Y n r).inr_isoPushout_inv]

/-- Both native pushout Isos identify the SAME finite latching-stage map. -/
def stageArrowIso {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    Arrow.mk (chosenMap eta n r) ≅ Arrow.mk (outerLatchingStageMap eta n r) := by
  exact Arrow.isoMk
    (outerLatchingStageSource_isPushout X n r).isoPushout.symm
    (outerLatchingStageSource_isPushout Y n r).isoPushout.symm
    (chosenMap_stage_transport eta n r)

/-- The four Arrow legs are exactly the two actual universal Isos and inverses. -/
theorem stageArrowIso_fourLegs {X Y : SimplicialObject SSet.{u}}
    (eta : X ⟶ Y) (n : ℕ) (r : Fin (n + 1)) :
    (stageArrowIso eta n r).hom.left = (outerLatchingStageSource_isPushout X n r).isoPushout.inv ∧
      (stageArrowIso eta n r).hom.right =
          (outerLatchingStageSource_isPushout Y n r).isoPushout.inv ∧
      (stageArrowIso eta n r).inv.left = (outerLatchingStageSource_isPushout X n r).isoPushout.hom ∧
      (stageArrowIso eta n r).inv.right =
          (outerLatchingStageSource_isPushout Y n r).isoPushout.hom := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end SSet.RezkFiniteLatchingPushout
