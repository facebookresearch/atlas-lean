/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SkeletalUnionProductAttachment

/-!
# Homotopy cartesian inclusion of skeletal attachment domains

Sharp row maps and weak relative comparisons for every simplex operator make the incoming square from the diagonal attachment domain into the coefficient row tensored with its standard simplex homotopy cartesian. The comparison is formed with the complete union-product domain map and its actual inclusion in every degree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkSkeletalAttachment
open SharpComparisonDraft RezkCompatiblePushout RezkSkeletalProduct

private theorem hc_transport_eq {A X B Y : SSet.{u}}
    {f f' : A ⟶ X} {s s' : A ⟶ B} {p p' : X ⟶ Y} {g g' : B ⟶ Y}
    (sq : CommSq f s p g) (sq' : CommSq f' s' p' g')
    (hf : f = f') (hs : s = s') (hp : p = p') (hg : g = g')
    (hc : WeakEquivalence (pullback.lift f' s' sq'.w ≫ comparison p' g')) :
    WeakEquivalence (pullback.lift f s sq.w ≫ comparison p g) := by
  exact (hc_weakSquare_iff sq sq' (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id, Category.id_comp] using hf)
    (by simpa only [Category.comp_id, Category.id_comp] using hs)
    (by simpa only [Category.comp_id, Category.id_comp] using hp)
    (by simpa only [Category.comp_id, Category.id_comp] using hg)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr hc

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The actual union-product domain inclusion into the original row cell is
HC, derived from the three original pieces. Original row Sharp and ALL
operator comparisons are the only homotopical inputs. The domain/cell
comparison need not be mono or fibrant. -/
theorem attachment_domain_incoming_from_original_all_operators
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ n : SimplexCategory, Sharp (eta.app (op n)))
    (hoperators : ∀ {n m : SimplexCategory} (f : n ⟶ m),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f)) (n : ℕ) :
    WeakEquivalence
      (pullback.lift (diagonalAttachmentDomain X n).ι (diagonalAttachmentDomainMap eta n)
        (diagonalAttachmentDomainMap_ι eta n).symm ≫
        comparison (eta.app (op ⦋n + 1⦌) ▷ Δ[n + 1]) (diagonalAttachmentDomain Y n).ι) := by
  have latching := RezkFullLatching.sharp_and_incoming_from_original_all_operators
    eta hrows hoperators n
  let LX := outerLatching X (n + 1)
  let LY := outerLatching Y (n + 1)
  let B := boundary (n + 1)
  let K : SSet.{u} := Δ[n + 1]
  let rowX := X.obj (op ⦋n + 1⦌)
  let rowY := Y.obj (op ⦋n + 1⦌)
  let rowMap := eta.app (op ⦋n + 1⦌)
  let latchingMap := outerLatchingMap eta (n + 1)
  let tX : (LX : SSet.{u}) ⊗ B ⟶ rowX ⊗ B := LX.ι ▷ (B : SSet.{u})
  let iX : (LX : SSet.{u}) ⊗ B ⟶ (LX : SSet.{u}) ⊗ K := (LX : SSet.{u}) ◁ B.ι
  let tY : (LY : SSet.{u}) ⊗ B ⟶ rowY ⊗ B := LY.ι ▷ (B : SSet.{u})
  let iY : (LY : SSet.{u}) ⊗ B ⟶ (LY : SSet.{u}) ⊗ K := (LY : SSet.{u}) ◁ B.ι
  let rX := Subcomplex.unionProd.ι₁ LX B
  let bX := Subcomplex.unionProd.ι₂ LX B
  let rY := Subcomplex.unionProd.ι₁ LY B
  let bY := Subcomplex.unionProd.ι₂ LY B
  let p0 := latchingMap ▷ (B : SSet.{u})
  let p1 := rowMap ▷ (B : SSet.{u})
  let p2 := latchingMap ▷ K
  let p := diagonalAttachmentDomainMap eta n
  let jX := (diagonalAttachmentDomain X n).ι
  let jY := (diagonalAttachmentDomain Y n).ι
  let q := rowMap ▷ K
  have hl : tX ≫ p1 = p0 ≫ tY := by
    dsimp [tX, p1, p0, tY, latchingMap, rowMap, LX, LY]
    simp only [← comp_whiskerRight, outerLatchingMap_ι]
  have hr : iX ≫ p2 = p0 ≫ iY := whisker_exchange latchingMap B.ι
  have hR : rX ≫ p = p1 ≫ rY := boundary_piece_naturality eta n
  have hB : bX ≫ p = p2 ≫ bY := latching_piece_naturality eta n
  let whole : CommSq jX p q jY := CommSq.mk (diagonalAttachmentDomainMap_ι eta n).symm
  have h1X : rX ≫ jX = rowX ◁ B.ι := by
    dsimp only [rX, jX, LX, B, rowX, diagonalAttachmentDomain]
    exact Subcomplex.unionProd.ι₁_ι _ _
  have h1Y : rY ≫ jY = rowY ◁ B.ι := by
    dsimp only [rY, jY, LY, B, rowY, diagonalAttachmentDomain]
    exact Subcomplex.unionProd.ι₁_ι _ _
  have h2X : bX ≫ jX = LX.ι ▷ K := by
    dsimp only [bX, jX, LX, B, K, diagonalAttachmentDomain]
    exact Subcomplex.unionProd.ι₂_ι _ _
  have h2Y : bY ≫ jY = LY.ι ▷ K := by
    dsimp only [bY, jY, LY, B, K, diagonalAttachmentDomain]
    exact Subcomplex.unionProd.ι₂_ι _ _
  have boundaryNatural : (rowX ◁ B.ι) ≫ q = p1 ≫ (rowY ◁ B.ι) :=
    whisker_exchange rowMap B.ι
  let boundarySquare : CommSq (rowX ◁ B.ι) p1 q (rowY ◁ B.ι) := CommSq.mk boundaryNatural
  let piece1 : CommSq (rX ≫ jX) p1 q (rY ≫ jY) := CommSq.mk (by
    rw [h1X, h1Y]
    exact boundaryNatural)
  let piece2 : CommSq (bX ≫ jX) p2 q (bY ≫ jY) := CommSq.mk (by
    rw [h2X, h2Y]
    simp only [p2, q, ← comp_whiskerRight, latchingMap, rowMap, LX, LY, outerLatchingMap_ι])
  let rawPiece0 := (CommSq.mk hl).horiz_comp piece1
  let piece0 : CommSq ((tX ≫ rX) ≫ jX) p0 q ((tY ≫ rY) ≫ jY) := CommSq.mk (by
    simpa only [Category.assoc] using rawPiece0.w)
  have qSharp : Sharp q := tensor_map_sharp rowMap K (hrows ⦋n + 1⦌)
  have p1Sharp : Sharp p1 := tensor_map_sharp rowMap (B : SSet.{u}) (hrows ⦋n + 1⦌)
  have boundaryHC := tensor_boundary_hc rowMap B.ι (hrows ⦋n + 1⦌)
  have hc1 : WeakEquivalence (pullback.lift (rX ≫ jX) p1 piece1.w ≫ comparison q (rY ≫ jY)) := by
    exact hc_transport_eq piece1 boundarySquare h1X rfl rfl h1Y boundaryHC
  let original : CommSq LX.ι latchingMap rowMap LY.ι :=
    CommSq.mk (outerLatchingMap_ι eta (n + 1)).symm
  have finiteBoundary := finite_tensor_hc original (hrows ⦋n + 1⦌) latching.2
    (K := (B : SSet.{u}))
  have finiteCell := finite_tensor_hc original (hrows ⦋n + 1⦌) latching.2 (K := K)
  let cellSquare : CommSq (LX.ι ⊗ₘ 𝟙 K) (latchingMap ⊗ₘ 𝟙 K)
      (rowMap ⊗ₘ 𝟙 K) (LY.ι ⊗ₘ 𝟙 K) := CommSq.mk (by
    simpa only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id] using
      congrArg (fun f => f ⊗ₘ 𝟙 K) original.w)
  have hc2 : WeakEquivalence (pullback.lift (bX ≫ jX) p2 piece2.w ≫ comparison q (bY ≫ jY)) := by
    exact hc_transport_eq piece2 cellSquare
      (by simpa only [tensorHom_id] using h2X)
      (by simp only [p2, tensorHom_id]) (by simp only [q, tensorHom_id])
      (by simpa only [tensorHom_id] using h2Y) finiteCell
  have firstHC : WeakEquivalence (pullback.lift tX p0 hl ≫ comparison p1 tY) := finiteBoundary
  have rectangleHC := (RezkIncomingHC.first_hc_iff_rectangle
    tX (rowX ◁ B.ι) p0 p1 q tY (rowY ◁ B.ι) hl boundaryNatural
    p1Sharp qSharp boundaryHC).mp firstHC
  have hc0 : WeakEquivalence
      (pullback.lift ((tX ≫ rX) ≫ jX) p0 piece0.w ≫ comparison q ((tY ≫ rY) ≫ jY)) := by
    have h0X : (tX ≫ rX) ≫ jX = tX ≫ (rowX ◁ B.ι) :=
      (Category.assoc tX rX jX).trans (congrArg (fun f => tX ≫ f) h1X)
    have h0Y : (tY ≫ rY) ≫ jY = tY ≫ (rowY ◁ B.ι) :=
      (Category.assoc tY rY jY).trans (congrArg (fun f => tY ≫ f) h1Y)
    exact hc_transport_eq piece0 ((CommSq.mk hl).horiz_comp boundarySquare)
      h0X rfl rfl h0Y rectangleHC
  let _ : Mono iX := by
    change Mono ((tensorLeft (LX : SSet.{u})).map B.ι)
    infer_instance
  let _ : Mono iY := by
    change Mono ((tensorLeft (LY : SSet.{u})).map B.ι)
    infer_instance
  exact RezkUnionIncomingHC.incoming_of_three_original_pieces
    (Subcomplex.unionProd.isPushout LX B) (Subcomplex.unionProd.isPushout LY B)
    p0 p1 p2 p jX jY q hl hr hR hB whole piece0 piece1 piece2 qSharp hc0 hc1 hc2

end SSet.RezkSkeletalAttachment
