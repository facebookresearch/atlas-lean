/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialSkeletalFiltration
import MathlibExt.AlgebraicTopology.SimplicialSet.IncomingHCPasting
import MathlibExt.CategoryTheory.Subfunctor.PreimagePullback

/-!
# Homotopy-cartesian comparisons in latching induction

The two incoming HC assertions in the actual source-overlap induction.

The left assertion is DERIVED by pasting the already inductive overlap-to-row
assertion with the original row operator, then cancelling the inductive
prior-stage inclusion. No left-HC goal or diagonal outcome is an input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkIncomingHC
open SharpComparisonDraft

/-- Derive the original overlap-to-prior-stage HC square from the precise
row/operator and incoming invariants of the double latching induction. -/
theorem source_top_hc_of_source_left
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) (r : Fin (n + 1))
    (hpRow : Sharp (eta.app (op ⦋n⦌)))
    (hpNext : Sharp (eta.app (op ⦋n + 1⦌)))
    (hpBefore : Sharp (outerLatchingStageBeforeMap eta n r))
    (rowOperatorHC : WeakEquivalence
      (pullback.lift (X.σ r) (eta.app (op ⦋n⦌))
        (SimplicialObject.σ_naturality eta r) ≫
        comparison (eta.app (op ⦋n + 1⦌)) (Y.σ r)))
    (overlapIncomingHC : WeakEquivalence
      (pullback.lift (outerLatchingStageSourceOverlap X n r).ι
        (outerLatchingStageSourceOverlapMap eta n r)
        (outerLatchingStageSource_left_naturality eta n r).symm ≫
        comparison (eta.app (op ⦋n⦌)) (outerLatchingStageSourceOverlap Y n r).ι))
    (beforeIncomingHC : WeakEquivalence
      (pullback.lift (outerLatchingStageBefore X n r).ι
        (outerLatchingStageBeforeMap eta n r)
        (outerLatchingStageBeforeMap_ι eta n r).symm ≫
        comparison (eta.app (op ⦋n + 1⦌)) (outerLatchingStageBefore Y n r).ι)) :
    WeakEquivalence
      (pullback.lift ((outerLatchingStageBefore X n r).fromPreimage (X.σ r))
        (outerLatchingStageSourceOverlapMap eta n r)
        (outerLatchingStageSource_top_naturality eta n r).symm ≫
        comparison (outerLatchingStageBeforeMap eta n r)
          ((outerLatchingStageBefore Y n r).fromPreimage (Y.σ r))) := by
  have rectangle := (first_hc_iff_rectangle
    (outerLatchingStageSourceOverlap X n r).ι (X.σ r)
    (outerLatchingStageSourceOverlapMap eta n r)
    (eta.app (op ⦋n⦌)) (eta.app (op ⦋n + 1⦌))
    (outerLatchingStageSourceOverlap Y n r).ι (Y.σ r)
    (outerLatchingStageSource_left_naturality eta n r).symm
    (SimplicialObject.σ_naturality eta r) hpRow hpNext rowOperatorHC).mp overlapIncomingHC
  apply (first_hc_iff_rectangle
    ((outerLatchingStageBefore X n r).fromPreimage (X.σ r))
    (outerLatchingStageBefore X n r).ι
    (outerLatchingStageSourceOverlapMap eta n r)
    (outerLatchingStageBeforeMap eta n r) (eta.app (op ⦋n + 1⦌))
    ((outerLatchingStageBefore Y n r).fromPreimage (Y.σ r))
    (outerLatchingStageBefore Y n r).ι
    (outerLatchingStageSource_top_naturality eta n r).symm
    (outerLatchingStageBeforeMap_ι eta n r).symm
    hpBefore hpNext beforeIncomingHC).mpr
  simpa only [Subcomplex.fromPreimage_ι] using rectangle

/-- At a successor index the actual overlap-to-row HC assertion is the
lower-degree latching incoming assertion through the two literal subcomplex Isos. -/
theorem source_succ_left_hc_iff_stage_incoming
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    WeakEquivalence
      (pullback.lift (outerLatchingStageSourceOverlap X (n + 1) r.succ).ι
        (outerLatchingStageSourceOverlapMap eta (n + 1) r.succ)
        (outerLatchingStageSource_left_naturality eta (n + 1) r.succ).symm ≫
        comparison (eta.app (op ⦋n + 1⦌))
          (outerLatchingStageSourceOverlap Y (n + 1) r.succ).ι) ↔
      WeakEquivalence
        (pullback.lift (outerLatchingStage X n r).ι (outerLatchingStageMap eta n r)
          (outerLatchingStageMap_ι eta n r).symm ≫
          comparison (eta.app (op ⦋n + 1⦌)) (outerLatchingStage Y n r).ι) := by
  let ex := Subcomplex.eqToIso (outerLatchingStageSourceOverlap_succ X n r)
  let ey := Subcomplex.eqToIso (outerLatchingStageSourceOverlap_succ Y n r)
  have hmap : outerLatchingStageSourceOverlapMap eta (n + 1) r.succ ≫ ey.hom =
      ex.hom ≫ outerLatchingStageMap eta n r := by
    apply (cancel_mono (outerLatchingStage Y n r).ι).mp
    simp [ex, ey, Category.assoc]
  exact RezkCompatiblePushout.hc_weakSquare_iff
    (CommSq.mk (outerLatchingStageSource_left_naturality eta (n + 1) r.succ).symm)
    (CommSq.mk (outerLatchingStageMap_ι eta n r).symm)
    ex.hom (𝟙 _) ey.hom (𝟙 _)
    (by simp [ex]) hmap (by simp) (by simp [ey])
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)

/-- The zero overlap is the actual empty preimage square. Its original HC
assertion follows from row sharpness and that strict universal property. -/
theorem source_zero_left_hc
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ)
    (hpRow : Sharp (eta.app (op ⦋n⦌))) :
    WeakEquivalence
      (pullback.lift (outerLatchingStageSourceOverlap X n 0).ι
        (outerLatchingStageSourceOverlapMap eta n 0)
        (outerLatchingStageSource_left_naturality eta n 0).symm ≫
        comparison (eta.app (op ⦋n⦌)) (outerLatchingStageSourceOverlap Y n 0).ι) := by
  let A : (Y.obj (op ⦋n⦌)).Subcomplex := ⊥
  have hx : outerLatchingStageSourceOverlap X n 0 = A.preimage (eta.app (op ⦋n⦌)) := by
    rw [outerLatchingStageSourceOverlap_zero]
    ext a x
    simp [A, Subcomplex.preimage_obj]
  have hy : outerLatchingStageSourceOverlap Y n 0 = A :=
    outerLatchingStageSourceOverlap_zero Y n
  let ex := Subcomplex.eqToIso hx
  let ey := Subcomplex.eqToIso hy
  have hmap : outerLatchingStageSourceOverlapMap eta n 0 ≫ ey.hom =
      ex.hom ≫ A.fromPreimage (eta.app (op ⦋n⦌)) := by
    apply (cancel_mono A.ι).mp
    simp [ex, ey, Category.assoc]
  have strict : IsPullback (A.preimage (eta.app (op ⦋n⦌))).ι
      (A.fromPreimage (eta.app (op ⦋n⦌))) (eta.app (op ⦋n⦌)) A.ι := by
    exact CategoryTheory.Subfunctor.preimage_isPullback A (eta.app (op ⦋n⦌))
  have hc := RezkCompatiblePushout.strictSquare_hc strict hpRow
  exact (RezkCompatiblePushout.hc_weakSquare_iff
    (CommSq.mk (outerLatchingStageSource_left_naturality eta n 0).symm) strict.toCommSq
    ex.hom (𝟙 _) ey.hom (𝟙 _)
    (by simp [ex]) hmap (by simp) (by simp [ey])
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr hc

end SSet.RezkIncomingHC
