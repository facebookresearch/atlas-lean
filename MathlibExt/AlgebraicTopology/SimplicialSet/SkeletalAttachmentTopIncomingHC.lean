/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteBoundaryIncomingHC
import MathlibExt.AlgebraicTopology.SimplicialSet.WholeLatchingToOldStageHC

/-!
# Incoming comparison for the top map of a skeletal attachment

The top map from a diagonal skeletal attachment domain into the preceding skeleton has a weak pullback-to-homotopy-pullback comparison for a simplicial diagram map with sharp rows and weak relative comparisons for every simplex operator, provided the preceding stage invariant holds. The comparison retains the full union-product attachment-domain map and its naturality square.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkSkeletalAttachment
open SharpComparisonDraft RezkSkeletalCell RezkSkeletalProduct RezkBoundaryOldStage
    RezkLatchingOldStage

private theorem hc_transport_eq {A X B Y : SSet.{u}}
    {f f' : A ⟶ X} {s : A ⟶ B} {p : X ⟶ Y} {g g' : B ⟶ Y}
    (sq : CommSq f s p g) (sq' : CommSq f' s p g') (hf : f = f') (hg : g = g')
    (hc : WeakEquivalence (pullback.lift f' s sq'.w ≫ comparison p g')) :
    WeakEquivalence (pullback.lift f s sq.w ≫ comparison p g) := by
  exact (RezkCompatiblePushout.hc_weakSquare_iff sq sq' (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id, Category.id_comp] using hf)
    (by simp) (by simp)
    (by simpa only [Category.comp_id, Category.id_comp] using hg)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr hc

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The ACTUAL attaching map into the old skeleton is HC. Both its boundary
and latching halves and their original overlap are derived; no comparison
Mono, attachment HC or successor-stage Sharp outcome is supplied. -/
theorem attachment_top_hc_from_actual_prior_invariant
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f))
    (n : ℕ) (previous : stageCellInvariant eta n) :
    WeakEquivalence
      (pullback.lift (diagonalAttachmentTopMap X n) (diagonalAttachmentDomainMap eta n)
        (diagonalAttachmentTopMap_naturality eta n).symm ≫
        comparison (diagonalFiltrationNatMap eta n) (diagonalAttachmentTopMap Y n)) := by
  let LX := outerLatching X (n + 1)
  let LY := outerLatching Y (n + 1)
  let B := boundary (n + 1)
  let K : SSet.{u} := Δ[n + 1]
  let tX := LX.ι ▷ (B : SSet.{u})
  let iX := (LX : SSet.{u}) ◁ B.ι
  let rX := Subcomplex.unionProd.ι₁ LX B
  let bX := Subcomplex.unionProd.ι₂ LX B
  let tY := LY.ι ▷ (B : SSet.{u})
  let iY := (LY : SSet.{u}) ◁ B.ι
  let rY := Subcomplex.unionProd.ι₁ LY B
  let bY := Subcomplex.unionProd.ι₂ LY B
  let lmap := outerLatchingMap eta (n + 1)
  let p0 := lmap ▷ (B : SSet.{u})
  let p1 := eta.app (op ⦋n + 1⦌) ▷ (B : SSet.{u})
  let p2 := lmap ▷ K
  let p := diagonalAttachmentDomainMap eta n
  let jX := diagonalAttachmentTopMap X n
  let jY := diagonalAttachmentTopMap Y n
  let q := diagonalFiltrationNatMap eta n
  have hl : tX ≫ p1 = p0 ≫ tY := by
    simp only [tX, p1, p0, tY, lmap, LX, LY, ← comp_whiskerRight, outerLatchingMap_ι]
  have hr : iX ≫ p2 = p0 ≫ iY := whisker_exchange lmap B.ι
  have hR : rX ≫ p = p1 ≫ rY := boundary_piece_naturality eta n
  have hB : bX ≫ p = p2 ≫ bY := latching_piece_naturality eta n
  let whole : CommSq jX p q jY := CommSq.mk (diagonalAttachmentTopMap_naturality eta n).symm
  have h1X : rX ≫ jX = toOldStage X n B le_rfl := by
    simp only [rX, jX, LX, B, toOldStage, Subcomplex.homOfLE_refl,
      whiskerLeft_id, Category.id_comp]
  have h1Y : rY ≫ jY = toOldStage Y n B le_rfl := by
    simp only [rY, jY, LY, B, toOldStage, Subcomplex.homOfLE_refl,
      whiskerLeft_id, Category.id_comp]
  let piece1 : CommSq (rX ≫ jX) p1 q (rY ≫ jY) := CommSq.mk (by
    rw [h1X, h1Y]
    exact toOldStage_naturality eta n B le_rfl)
  let piece2 : CommSq (bX ≫ jX) p2 q (bY ≫ jY) := CommSq.mk (wholeToOld_naturality eta n)
  let rawPiece0 := (CommSq.mk hl).horiz_comp piece1
  let piece0 : CommSq ((tX ≫ rX) ≫ jX) p0 q ((tY ≫ rY) ≫ jY) := CommSq.mk (by
    simpa only [Category.assoc] using rawPiece0.w)
  have hc1 : WeakEquivalence (pullback.lift _ _ piece1.w ≫ comparison q _) := by
    exact hc_transport_eq piece1 (CommSq.mk (toOldStage_naturality eta n B le_rfl))
      h1X h1Y
      (RezkFiniteBoundaryIncoming.whole_boundary_incoming_hc eta hrows hoperators n previous)
  have hc2 : WeakEquivalence (pullback.lift _ _ piece2.w ≫ comparison q _) :=
    whole_latching_to_old_hc eta hrows hoperators n previous
  have latching := RezkFullLatching.sharp_and_incoming_from_original_all_operators eta hrows
      hoperators n
  have p2Sharp : Sharp p2 := tensor_map_sharp lmap K latching.1
  have first := tensor_boundary_hc lmap B.ι latching.1
  have rectangle := (RezkIncomingHC.first_hc_iff_rectangle
    iX (bX ≫ jX) p0 p2 q iY (bY ≫ jY) hr piece2.w p2Sharp previous.1 hc2).mp first
  have commX : tX ≫ rX = iX ≫ bX := (Subcomplex.unionProd.isPushout LX B).w
  have commY : tY ≫ rY = iY ≫ bY := (Subcomplex.unionProd.isPushout LY B).w
  have source_path : (tX ≫ rX) ≫ jX = iX ≫ (bX ≫ jX) := by
    exact (congrArg (fun f => f ≫ jX) commX).trans (Category.assoc iX bX jX)
  have target_path : (tY ≫ rY) ≫ jY = iY ≫ (bY ≫ jY) := by
    exact (congrArg (fun f => f ≫ jY) commY).trans (Category.assoc iY bY jY)
  let pathSquare := (CommSq.mk hr).horiz_comp piece2
  have hc0 : WeakEquivalence (pullback.lift _ _ piece0.w ≫ comparison q _) := by
    exact hc_transport_eq piece0 pathSquare source_path target_path rectangle
  let _ : Mono iX := by
    change Mono ((tensorLeft (LX : SSet.{u})).map B.ι)
    infer_instance
  let _ : Mono iY := by
    change Mono ((tensorLeft (LY : SSet.{u})).map B.ι)
    infer_instance
  exact RezkUnionIncomingHC.incoming_of_three_original_pieces
    (Subcomplex.unionProd.isPushout LX B) (Subcomplex.unionProd.isPushout LY B)
    p0 p1 p2 p jX jY q hl hr hR hB whole piece0 piece1 piece2 previous.1 hc0 hc1 hc2

end SSet.RezkSkeletalAttachment
