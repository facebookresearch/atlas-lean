/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.LatchingOldStageInductionGeometry
import MathlibExt.AlgebraicTopology.SimplicialSet.UnionIncomingHC

/-!
# Gluing finite latching comparisons into the preceding skeleton

A weak comparison for the piece before a degeneracy attachment extends to its complete finite latching stage by gluing the degeneracy image along its source overlap. This extension assumes sharp row maps, weak relative comparisons for all simplex operators, and the preceding diagonal stage invariant, and concludes weakness of the canonical finite-stage-to-skeleton comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkLatchingOldStage
open SharpComparisonDraft RezkSkeletalCell RezkCompatiblePushout

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

/-- The current finite degeneracy union is HC to the old skeleton.
Only its actual preceding finite HC (the inner induction hypothesis) is
carried. The range and source-overlap HC assertions are derived internally. -/
theorem stage_hc_from_actual_before {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f))
    (n : ℕ) (r : Fin (n + 1)) (previous : stageCellInvariant eta n)
    (beforeHC : WeakEquivalence
      (pullback.lift (beforeToOld X n r) (outerLatchingStageBeforeMap eta n r ▷ Δ[n + 1])
        (beforeToOld_naturality eta n r) ≫
        comparison (diagonalFiltrationNatMap eta n) (beforeToOld Y n r))) :
    WeakEquivalence
      (pullback.lift (stageToOld X n r) (outerLatchingStageMap eta n r ▷ Δ[n + 1])
        (stageToOld_naturality eta n r) ≫
        comparison (diagonalFiltrationNatMap eta n) (stageToOld Y n r)) := by
  let K : SSet.{u} := Δ[n + 1]
  let sx := (outerLatchingStageSource_isPushout X n r).map (tensorRight K)
  let sy := (outerLatchingStageSource_isPushout Y n r).map (tensorRight K)
  let tX := (outerLatchingStageBefore X n r).fromPreimage (X.σ r) ▷ K
  let iX := (outerLatchingStageSourceOverlap X n r).ι ▷ K
  let rX : (outerLatchingStageBefore X n r : SSet.{u}) ⊗ K ⟶
      (outerLatchingStage X n r : SSet.{u}) ⊗ K :=
    (Subcomplex.homOfLE (by rw [outerLatchingStage_eq_before_sup_range]; exact le_sup_left)) ▷ K
  let bX := outerDegeneracyToLatchingStage X n r ▷ K
  let tY := (outerLatchingStageBefore Y n r).fromPreimage (Y.σ r) ▷ K
  let iY := (outerLatchingStageSourceOverlap Y n r).ι ▷ K
  let rY : (outerLatchingStageBefore Y n r : SSet.{u}) ⊗ K ⟶
      (outerLatchingStage Y n r : SSet.{u}) ⊗ K :=
    (Subcomplex.homOfLE (by rw [outerLatchingStage_eq_before_sup_range]; exact le_sup_left)) ▷ K
  let bY := outerDegeneracyToLatchingStage Y n r ▷ K
  let p0 := outerLatchingStageSourceOverlapMap eta n r ▷ K
  let p1 := outerLatchingStageBeforeMap eta n r ▷ K
  let p2 := eta.app (op ⦋n⦌) ▷ K
  let p := outerLatchingStageMap eta n r ▷ K
  let jX := stageToOld X n r
  let jY := stageToOld Y n r
  let q := diagonalFiltrationNatMap eta n
  have hl : tX ≫ p1 = p0 ≫ tY := by
    simp only [tX, p1, p0, tY, ← comp_whiskerRight]
    exact congrArg (fun f => f ▷ K) (outerLatchingStageSource_top_naturality eta n r).symm
  have hr : iX ≫ p2 = p0 ≫ iY := by
    simp only [iX, p2, p0, iY, ← comp_whiskerRight]
    exact congrArg (fun f => f ▷ K) (outerLatchingStageSource_left_naturality eta n r).symm
  have hR : rX ≫ p = p1 ≫ rY := by
    simp only [rX, p, p1, rY, ← comp_whiskerRight]
    exact congrArg (fun f => f ▷ K) (outerLatchingStageSource_right_naturality eta n r).symm
  have hB : bX ≫ p = p2 ≫ bY := by
    simp only [bX, p, p2, bY, ← comp_whiskerRight]
    exact congrArg (fun f => f ▷ K) (outerLatchingStageSource_bottom_naturality eta n r).symm
  let whole : CommSq jX p q jY := CommSq.mk (stageToOld_naturality eta n r)
  have h1X : rX ≫ jX = beforeToOld X n r := rfl
  have h1Y : rY ≫ jY = beforeToOld Y n r := rfl
  have h2X : bX ≫ jX = degeneracyToOld X n r := degeneracy_stage_factor X n r
  have h2Y : bY ≫ jY = degeneracyToOld Y n r := degeneracy_stage_factor Y n r
  have commX : tX ≫ rX = iX ≫ bX := sx.w
  have commY : tY ≫ rY = iY ≫ bY := sy.w
  have h0X : (tX ≫ rX) ≫ jX = sourceOverlapToOld X n r := by
    rw [commX, Category.assoc, h2X]
    rfl
  have h0Y : (tY ≫ rY) ≫ jY = sourceOverlapToOld Y n r := by
    rw [commY, Category.assoc, h2Y]
    rfl
  let piece0 : CommSq ((tX ≫ rX) ≫ jX) p0 q ((tY ≫ rY) ≫ jY) := CommSq.mk (by
    rw [h0X, h0Y]
    exact sourceOverlapToOld_naturality eta n r)
  let piece1 : CommSq (rX ≫ jX) p1 q (rY ≫ jY) := CommSq.mk (by
    rw [h1X, h1Y]
    exact beforeToOld_naturality eta n r)
  let piece2 : CommSq (bX ≫ jX) p2 q (bY ≫ jY) := CommSq.mk (by
    rw [h2X, h2Y]
    exact degeneracyToOld_naturality eta n r)
  have hc0 : WeakEquivalence (pullback.lift _ _ piece0.w ≫ comparison q _) := by
    exact hc_transport_eq piece0 (CommSq.mk (sourceOverlapToOld_naturality eta n r))
      h0X h0Y (sourceOverlapToOld_hc eta hrows hoperators n r previous)
  have hc1 : WeakEquivalence (pullback.lift _ _ piece1.w ≫ comparison q _) := by
    exact hc_transport_eq piece1 (CommSq.mk (beforeToOld_naturality eta n r))
      h1X h1Y beforeHC
  have hc2 : WeakEquivalence (pullback.lift _ _ piece2.w ≫ comparison q _) := by
    exact hc_transport_eq piece2 (CommSq.mk (degeneracyToOld_naturality eta n r))
      h2X h2Y (degeneracyToOld_hc eta hrows n r previous)
  exact RezkUnionIncomingHC.incoming_of_three_original_pieces
    sx sy p0 p1 p2 p jX jY q hl hr hR hB whole piece0 piece1 piece2 previous.1 hc0 hc1 hc2

end SSet.RezkLatchingOldStage
