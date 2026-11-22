/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.RezkDiagonalSharpBase
import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteLatchingPushoutArrow
import MathlibExt.AlgebraicTopology.SimplicialSet.LatchingIncomingHC
import MathlibExt.AlgebraicTopology.SimplicialSet.CompatiblePushoutSharp
import MathlibExt.AlgebraicTopology.SimplicialSet.UnionIncomingHC

/-!
# Sharpness and homotopy-cartesian comparisons of finite latching stages

The actual finite latching invariant: stage Sharp AND its ambient incoming HC.

The zero stage is derived from the original row and sigma operator. The
successor sharpness uses actual prior/lower induction and the original
compatible pushout. No sharpness of the successor stage is supplied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkFiniteStageInvariant
open SharpComparisonDraft RezkCompatiblePushout RezkIncomingHC

private theorem hc_transport_eq {A X B Y : SSet.{u}}
    {f f' : A ⟶ X} {s : A ⟶ B} {p : X ⟶ Y} {g g' : B ⟶ Y}
    (sq : CommSq f s p g) (sq' : CommSq f' s p g') (hf : f = f') (hg : g = g')
    (hc : WeakEquivalence (pullback.lift f' s sq'.w ≫ comparison p g')) :
    WeakEquivalence (pullback.lift f s sq.w ≫ comparison p g) := by
  exact (hc_weakSquare_iff sq sq' (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id, Category.id_comp] using hf)
    (by simp) (by simp)
    (by simpa only [Category.comp_id, Category.id_comp] using hg)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr hc

/-- The real first stage derives both invariant fields from the original
row and its original zero-degeneracy HC square. -/
theorem zero_stage_sharp_and_incoming
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ)
    (hpRow : Sharp (eta.app (op ⦋n⦌)))
    (rowHC : WeakEquivalence
      (pullback.lift (X.σ (0 : Fin (n + 1))) (eta.app (op ⦋n⦌))
        (SimplicialObject.σ_naturality eta (0 : Fin (n + 1))) ≫
        comparison (eta.app (op ⦋n + 1⦌)) (Y.σ (0 : Fin (n + 1))))) :
    Sharp (outerLatchingStageMap eta n 0) ∧
      WeakEquivalence
        (pullback.lift (outerLatchingStage X n 0).ι (outerLatchingStageMap eta n 0)
          (outerLatchingStageMap_ι eta n 0).symm ≫
          comparison (eta.app (op ⦋n + 1⦌)) (outerLatchingStage Y n 0).ι) := by
  have hx : (outerLatchingStage_zero_iso X n).hom ≫ (outerLatchingStage X n 0).ι =
      X.σ (0 : Fin (n + 1)) := outerLatchingStage_zero_iso_hom_ι X n
  have hy : (outerLatchingStage_zero_iso Y n).hom ≫ (outerLatchingStage Y n 0).ι =
      Y.σ (0 : Fin (n + 1)) := outerLatchingStage_zero_iso_hom_ι Y n
  have hs : eta.app (op ⦋n⦌) ≫ (outerLatchingStage_zero_iso Y n).hom =
      (outerLatchingStage_zero_iso X n).hom ≫ outerLatchingStageMap eta n 0 := by
    apply (cancel_mono (outerLatchingStage Y n 0).ι).mp
    rw [Category.assoc, hy, Category.assoc, outerLatchingStageMap_ι,
      ← Category.assoc, hx]
    exact (SimplicialObject.σ_naturality eta (0 : Fin (n + 1))).symm
  have iffHC := hc_weakSquare_iff
    (CommSq.mk (SimplicialObject.σ_naturality eta (0 : Fin (n + 1))))
    (CommSq.mk (outerLatchingStageMap_ι eta n 0).symm)
    (outerLatchingStage_zero_iso X n).hom (𝟙 _)
    (outerLatchingStage_zero_iso Y n).hom (𝟙 _)
    (by simpa using hx.symm) hs (by simp) (by simpa using hy.symm)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)
  exact ⟨RezkDiagonalSharpBase.zeroStageMap_sharp eta n hpRow, iffHC.mp rowHC⟩

/-- The current finite-stage Sharp field is DERIVED from the actual earlier
stage, lower-degree overlap and original row/operator invariants. -/
theorem stage_sharp_of_original_induction_inputs
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) (r : Fin (n + 1))
    (hpRow : Sharp (eta.app (op ⦋n⦌)))
    (hpNext : Sharp (eta.app (op ⦋n + 1⦌)))
    (hpBefore : Sharp (outerLatchingStageBeforeMap eta n r))
    (hpOverlap : Sharp (outerLatchingStageSourceOverlapMap eta n r))
    (rowHC : WeakEquivalence
      (pullback.lift (X.σ r) (eta.app (op ⦋n⦌))
        (SimplicialObject.σ_naturality eta r) ≫
        comparison (eta.app (op ⦋n + 1⦌)) (Y.σ r)))
    (overlapHC : WeakEquivalence
      (pullback.lift (outerLatchingStageSourceOverlap X n r).ι
        (outerLatchingStageSourceOverlapMap eta n r)
        (outerLatchingStageSource_left_naturality eta n r).symm ≫
        comparison (eta.app (op ⦋n⦌)) (outerLatchingStageSourceOverlap Y n r).ι))
    (beforeHC : WeakEquivalence
      (pullback.lift (outerLatchingStageBefore X n r).ι
        (outerLatchingStageBeforeMap eta n r)
        (outerLatchingStageBeforeMap_ι eta n r).symm ≫
        comparison (eta.app (op ⦋n + 1⦌)) (outerLatchingStageBefore Y n r).ι)) :
    Sharp (outerLatchingStageMap eta n r) := by
  have leftHC := source_top_hc_of_source_left eta n r
    hpRow hpNext hpBefore rowHC overlapHC beforeHC
  have h := sharp_compatible_pushout
    ((outerLatchingStageBefore X n r).fromPreimage (X.σ r))
    (outerLatchingStageSourceOverlap X n r).ι
    ((outerLatchingStageBefore Y n r).fromPreimage (Y.σ r))
    (outerLatchingStageSourceOverlap Y n r).ι
    (outerLatchingStageSourceOverlapMap eta n r)
    (outerLatchingStageBeforeMap eta n r) (eta.app (op ⦋n⦌))
    (outerLatchingStageSource_top_naturality eta n r).symm
    (outerLatchingStageSource_left_naturality eta n r).symm
    hpOverlap hpBefore hpRow leftHC overlapHC
  have chosenSharp : Sharp (RezkFiniteLatchingPushout.chosenMap eta n r) := h.1
  exact (SharpCoproductClosure.sharp_arrowIso_iff
    (RezkFiniteLatchingPushout.stageArrowIso eta n r)).mp chosenSharp

/-- The current stage's ambient incoming HC field is DERIVED from the
actual preceding-stage, row and overlap incoming assertions. -/
theorem stage_incoming_of_original_piece_invariants
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) (r : Fin (n + 1))
    (hpRow : Sharp (eta.app (op ⦋n⦌)))
    (hpNext : Sharp (eta.app (op ⦋n + 1⦌)))
    (rowHC : WeakEquivalence
      (pullback.lift (X.σ r) (eta.app (op ⦋n⦌))
        (SimplicialObject.σ_naturality eta r) ≫
        comparison (eta.app (op ⦋n + 1⦌)) (Y.σ r)))
    (overlapHC : WeakEquivalence
      (pullback.lift (outerLatchingStageSourceOverlap X n r).ι
        (outerLatchingStageSourceOverlapMap eta n r)
        (outerLatchingStageSource_left_naturality eta n r).symm ≫
        comparison (eta.app (op ⦋n⦌)) (outerLatchingStageSourceOverlap Y n r).ι))
    (beforeHC : WeakEquivalence
      (pullback.lift (outerLatchingStageBefore X n r).ι
        (outerLatchingStageBeforeMap eta n r)
        (outerLatchingStageBeforeMap_ι eta n r).symm ≫
        comparison (eta.app (op ⦋n + 1⦌)) (outerLatchingStageBefore Y n r).ι)) :
    WeakEquivalence
      (pullback.lift (outerLatchingStage X n r).ι (outerLatchingStageMap eta n r)
        (outerLatchingStageMap_ι eta n r).symm ≫
        comparison (eta.app (op ⦋n + 1⦌)) (outerLatchingStage Y n r).ι) := by
  let rX : (outerLatchingStageBefore X n r : SSet.{u}) ⟶ outerLatchingStage X n r :=
    Subcomplex.homOfLE (by rw [outerLatchingStage_eq_before_sup_range]; exact le_sup_left)
  let rY : (outerLatchingStageBefore Y n r : SSet.{u}) ⟶ outerLatchingStage Y n r :=
    Subcomplex.homOfLE (by rw [outerLatchingStage_eq_before_sup_range]; exact le_sup_left)
  let tX := (outerLatchingStageBefore X n r).fromPreimage (X.σ r)
  let tY := (outerLatchingStageBefore Y n r).fromPreimage (Y.σ r)
  have rX_ι : rX ≫ (outerLatchingStage X n r).ι = (outerLatchingStageBefore X n r).ι := by
    simp [rX]
  have rY_ι : rY ≫ (outerLatchingStage Y n r).ι = (outerLatchingStageBefore Y n r).ι := by
    simp [rY]
  have sx : IsPushout tX (outerLatchingStageSourceOverlap X n r).ι rX
      (outerDegeneracyToLatchingStage X n r) := outerLatchingStageSource_isPushout X n r
  have sy : IsPushout tY (outerLatchingStageSourceOverlap Y n r).ι rY
      (outerDegeneracyToLatchingStage Y n r) := outerLatchingStageSource_isPushout Y n r
  let p0 := outerLatchingStageSourceOverlapMap eta n r
  let p1 := outerLatchingStageBeforeMap eta n r
  let whole := CommSq.mk (outerLatchingStageMap_ι eta n r).symm
  have rawRectangle :=
      (CommSq.mk (outerLatchingStageSource_left_naturality eta n r).symm).horiz_comp
    (CommSq.mk (SimplicialObject.σ_naturality eta r))
  have piece0 : CommSq ((tX ≫ rX) ≫ (outerLatchingStage X n r).ι) p0
      (eta.app (op ⦋n + 1⦌)) ((tY ≫ rY) ≫ (outerLatchingStage Y n r).ι) := by
    refine CommSq.mk ?_
    simpa only [Category.assoc, rX_ι, rY_ι, tX, tY, p0, Subcomplex.fromPreimage_ι] using
        rawRectangle.w
  have piece1 : CommSq (rX ≫ (outerLatchingStage X n r).ι) p1
      (eta.app (op ⦋n + 1⦌)) (rY ≫ (outerLatchingStage Y n r).ι) := by
    refine CommSq.mk ?_
    simpa only [rX_ι, rY_ι, p1] using (outerLatchingStageBeforeMap_ι eta n r).symm
  let piece2 := CommSq.mk (SimplicialObject.σ_naturality eta r)
  have absoluteOverlap := (first_hc_iff_rectangle
    (outerLatchingStageSourceOverlap X n r).ι (X.σ r) p0
    (eta.app (op ⦋n⦌)) (eta.app (op ⦋n + 1⦌))
    (outerLatchingStageSourceOverlap Y n r).ι (Y.σ r)
    (outerLatchingStageSource_left_naturality eta n r).symm
    (SimplicialObject.σ_naturality eta r) hpRow hpNext rowHC).mp overlapHC
  have hc0 : WeakEquivalence (pullback.lift _ _ piece0.w ≫ comparison _ _) := by
    have h0X : (tX ≫ rX) ≫ (outerLatchingStage X n r).ι =
        (outerLatchingStageSourceOverlap X n r).ι ≫ X.σ r := by
      rw [Category.assoc, rX_ι]
      exact Subcomplex.fromPreimage_ι _ _
    have h0Y : (tY ≫ rY) ≫ (outerLatchingStage Y n r).ι =
        (outerLatchingStageSourceOverlap Y n r).ι ≫ Y.σ r := by
      rw [Category.assoc, rY_ι]
      exact Subcomplex.fromPreimage_ι _ _
    exact hc_transport_eq piece0 rawRectangle h0X h0Y absoluteOverlap
  have hc1 : WeakEquivalence (pullback.lift _ _ piece1.w ≫ comparison _ _) := by
    exact hc_transport_eq piece1
      (CommSq.mk (outerLatchingStageBeforeMap_ι eta n r).symm) rX_ι rY_ι beforeHC
  have piece2' : CommSq
      (outerDegeneracyToLatchingStage X n r ≫ (outerLatchingStage X n r).ι)
      (eta.app (op ⦋n⦌)) (eta.app (op ⦋n + 1⦌))
      (outerDegeneracyToLatchingStage Y n r ≫ (outerLatchingStage Y n r).ι) := by
    refine CommSq.mk ?_
    simpa only [outerDegeneracyToLatchingStage_ι] using piece2.w
  have hc2 : WeakEquivalence (pullback.lift _ _ piece2'.w ≫ comparison _ _) := by
    exact hc_transport_eq piece2' piece2
      (outerDegeneracyToLatchingStage_ι X n r)
      (outerDegeneracyToLatchingStage_ι Y n r) rowHC
  exact RezkUnionIncomingHC.incoming_of_three_original_pieces sx sy p0 p1
    (eta.app (op ⦋n⦌)) (outerLatchingStageMap eta n r)
    (outerLatchingStage X n r).ι (outerLatchingStage Y n r).ι (eta.app (op ⦋n + 1⦌))
    (outerLatchingStageSource_top_naturality eta n r).symm
    (outerLatchingStageSource_left_naturality eta n r).symm
    (outerLatchingStageSource_right_naturality eta n r).symm
    (outerLatchingStageSource_bottom_naturality eta n r).symm
    whole piece0 piece1 piece2' hpNext hc0 hc1 hc2

end SSet.RezkFiniteStageInvariant
