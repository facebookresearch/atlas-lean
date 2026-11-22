/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BoundarySubcomplexToOldStage
import MathlibExt.AlgebraicTopology.SimplicialSet.UnionIncomingHC

/-!
# Homotopy cartesian comparisons for finite boundary face unions

For a map of simplicial diagrams with sharp row maps and weak relative comparisons for every simplex operator, the nth stage invariant gives weak incoming comparisons for every finite union of boundary faces in degree n + 1. Identifying the complete face union with the boundary yields the corresponding comparison for the whole boundary.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkFiniteBoundaryIncoming
open SharpComparisonDraft RezkSkeletalCell RezkBoundaryOldStage RezkFiniteFaceIncidence

private abbrev oldStageHC {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ)
    (A : (Δ[n + 1] : SSet.{u}).Subcomplex) (hA : A ≤ boundary (n + 1)) : Prop :=
  WeakEquivalence
    (pullback.lift (toOldStage X n A hA) (eta.app (op ⦋n + 1⦌) ▷ (A : SSet.{u}))
      (toOldStage_naturality eta n A hA) ≫
      comparison (diagonalFiltrationNatMap eta n) (toOldStage Y n A hA))

private theorem oldStageHC_congr {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ)
    {A B : (Δ[n + 1] : SSet.{u}).Subcomplex}
    (hA : A ≤ boundary (n + 1)) (hB : B ≤ boundary (n + 1)) (h : A = B) :
    oldStageHC eta n A hA ↔ oldStageHC eta n B hB := by
  subst B
  rfl

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

/-- Omitting the selected vertex gives an actual proper face, even when that
vertex was already omitted from S. -/
theorem erase_proper {n : ℕ} (S : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    S.erase j ⊂ Finset.univ := by
  refine lt_of_le_of_ne (Finset.subset_univ _) ?_
  intro eq
  have hj : j ∈ S.erase j := by rw [eq]; exact Finset.mem_univ j
  simp at hj

/-- Every selected-face union, including the empty one, lies in the actual
boundary. No restriction on S or a choice of simplex is required. -/
theorem faceUnion_le_boundary {n : ℕ} (S F : Finset (Fin (n + 2))) :
    faceUnion.{u} S F ≤ boundary (n + 1) := by
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  exact RezkProperFaceCell.properFace_le_boundary (S.erase j) (erase_proper S j)

/-- Finite incidence induction derives incoming HC for every old face union.
The induction is strengthened over ALL vertex subsets, so the exact next
overlap uses the same theorem at S.erase j, including empty intersections. -/
theorem every_face_union_hc {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f))
    (n : ℕ) (previous : stageCellInvariant eta n) :
    ∀ (F S : Finset (Fin (n + 2))), WeakEquivalence
      (pullback.lift (toOldStage X n (faceUnion S F) (faceUnion_le_boundary S F))
        (eta.app (op ⦋n + 1⦌) ▷ (faceUnion S F : SSet.{u}))
        (toOldStage_naturality eta n (faceUnion S F) (faceUnion_le_boundary S F)) ≫
        comparison (diagonalFiltrationNatMap eta n)
          (toOldStage Y n (faceUnion S F) (faceUnion_le_boundary S F))) := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
      intro S
      exact (oldStageHC_congr eta n (faceUnion_le_boundary S ∅) bot_le
        (faceUnion_empty S)).mpr (empty_hc eta n previous)
  | @insert j F hj ih =>
      intro S
      let I := faceUnion.{u} (S.erase j) F
      let O := faceUnion.{u} S F
      let C := stdSimplex.face.{u} (S.erase j)
      let U := faceUnion.{u} S (insert j F)
      have hI : I ≤ boundary (n + 1) := faceUnion_le_boundary (S.erase j) F
      have hO : O ≤ boundary (n + 1) := faceUnion_le_boundary S F
      have hC : C ≤ boundary (n + 1) :=
          RezkProperFaceCell.properFace_le_boundary (S.erase j) (erase_proper S j)
      have hU : U ≤ boundary (n + 1) := faceUnion_le_boundary S (insert j F)
      let incidence : Subcomplex.BicartSq I O C U :=
        { inf_eq := faceUnion_inter_next S F j
          sup_eq := (faceUnion_insert S F j).symm }
      let rowX := X.obj (op ⦋n + 1⦌)
      let rowY := Y.obj (op ⦋n + 1⦌)
      let a := eta.app (op ⦋n + 1⦌)
      let tX := rowX ◁ Subcomplex.homOfLE incidence.le₁₂
      let iX := rowX ◁ Subcomplex.homOfLE incidence.le₁₃
      let rX := rowX ◁ Subcomplex.homOfLE incidence.le₂₄
      let bX := rowX ◁ Subcomplex.homOfLE incidence.le₃₄
      let tY := rowY ◁ Subcomplex.homOfLE incidence.le₁₂
      let iY := rowY ◁ Subcomplex.homOfLE incidence.le₁₃
      let rY := rowY ◁ Subcomplex.homOfLE incidence.le₂₄
      let bY := rowY ◁ Subcomplex.homOfLE incidence.le₃₄
      let p0 := a ▷ (I : SSet.{u})
      let p1 := a ▷ (O : SSet.{u})
      let p2 := a ▷ (C : SSet.{u})
      let p := a ▷ (U : SSet.{u})
      let jX := toOldStage X n U hU
      let jY := toOldStage Y n U hU
      let q := diagonalFiltrationNatMap eta n
      have hl : tX ≫ p1 = p0 ≫ tY := whisker_exchange a (Subcomplex.homOfLE incidence.le₁₂)
      have hr : iX ≫ p2 = p0 ≫ iY := whisker_exchange a (Subcomplex.homOfLE incidence.le₁₃)
      have hR : rX ≫ p = p1 ≫ rY := whisker_exchange a (Subcomplex.homOfLE incidence.le₂₄)
      have hB : bX ≫ p = p2 ≫ bY := whisker_exchange a (Subcomplex.homOfLE incidence.le₃₄)
      let whole : CommSq jX p q jY := CommSq.mk (toOldStage_naturality eta n U hU)
      have h1X : rX ≫ jX = toOldStage X n O hO := inclusion_toOldStage X n hO hU incidence.le₂₄
      have h1Y : rY ≫ jY = toOldStage Y n O hO := inclusion_toOldStage Y n hO hU incidence.le₂₄
      have h2X : bX ≫ jX = toOldStage X n C hC := inclusion_toOldStage X n hC hU incidence.le₃₄
      have h2Y : bY ≫ jY = toOldStage Y n C hC := inclusion_toOldStage Y n hC hU incidence.le₃₄
      have h0X : (tX ≫ rX) ≫ jX = toOldStage X n I hI := by
        rw [Category.assoc, h1X]
        exact inclusion_toOldStage X n hI hO incidence.le₁₂
      have h0Y : (tY ≫ rY) ≫ jY = toOldStage Y n I hI := by
        rw [Category.assoc, h1Y]
        exact inclusion_toOldStage Y n hI hO incidence.le₁₂
      let piece0 : CommSq ((tX ≫ rX) ≫ jX) p0 q ((tY ≫ rY) ≫ jY) := CommSq.mk (by
        rw [h0X, h0Y]
        exact toOldStage_naturality eta n I hI)
      let piece1 : CommSq (rX ≫ jX) p1 q (rY ≫ jY) := CommSq.mk (by
        rw [h1X, h1Y]
        exact toOldStage_naturality eta n O hO)
      let piece2 : CommSq (bX ≫ jX) p2 q (bY ≫ jY) := CommSq.mk (by
        rw [h2X, h2Y]
        exact toOldStage_naturality eta n C hC)
      have hc0 : WeakEquivalence (pullback.lift _ _ piece0.w ≫ comparison q _) := by
        exact hc_transport_eq piece0 (CommSq.mk (toOldStage_naturality eta n I hI))
          h0X h0Y (ih (S.erase j))
      have hc1 : WeakEquivalence (pullback.lift _ _ piece1.w ≫ comparison q _) := by
        exact hc_transport_eq piece1 (CommSq.mk (toOldStage_naturality eta n O hO))
          h1X h1Y (ih S)
      have hc2 : WeakEquivalence (pullback.lift _ _ piece2.w ≫ comparison q _) := by
        exact hc_transport_eq piece2 (CommSq.mk (toOldStage_naturality eta n C hC))
          h2X h2Y (face_hc eta hrows hoperators n (S.erase j) (erase_proper S j) previous)
      let _ : Mono iX := by
        change Mono ((tensorLeft rowX).map (Subcomplex.homOfLE incidence.le₁₃))
        infer_instance
      let _ : Mono iY := by
        change Mono ((tensorLeft rowY).map (Subcomplex.homOfLE incidence.le₁₃))
        infer_instance
      exact RezkUnionIncomingHC.incoming_of_three_original_pieces
        (faceUnion_tensor_isPushout rowX S F j) (faceUnion_tensor_isPushout rowY S F j)
        p0 p1 p2 p jX jY q hl hr hR hB whole piece0 piece1 piece2 previous.1 hc0 hc1 hc2

/-- The whole actual boundary-to-old-skeleton square is HC, with every
face, overlap and collapsed inner operator retained. -/
theorem whole_boundary_incoming_hc {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f))
    (n : ℕ) (previous : stageCellInvariant eta n) :
    WeakEquivalence
      (pullback.lift (toOldStage X n (boundary (n + 1)) le_rfl)
        (eta.app (op ⦋n + 1⦌) ▷ (boundary (n + 1) : SSet.{u}))
        (toOldStage_naturality eta n (boundary (n + 1)) le_rfl) ≫
        comparison (diagonalFiltrationNatMap eta n)
            (toOldStage Y n (boundary (n + 1)) le_rfl)) := by
  exact (oldStageHC_congr eta n (faceUnion_le_boundary Finset.univ Finset.univ)
    le_rfl (faceUnion_all (n + 1))).mp
      (every_face_union_hc eta hrows hoperators n previous Finset.univ Finset.univ)

end SSet.RezkFiniteBoundaryIncoming
