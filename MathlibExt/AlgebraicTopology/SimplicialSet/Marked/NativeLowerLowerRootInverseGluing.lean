/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeLowerLowerRootFace
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeLowerDoubleCofaceRoot

/-!
# Genuine gluing on complete original lower/lower root intersections

The full original marked double-coface cone image identifies the entire
original two-lower-coordinate intersection. Both unchanged coordinate
projections retain their original coface images. The actual native
double-coface unit equation therefore makes the two lower inverse maps
agree on that complete marked intersection inside the original native
boundary source. No native boundary source map is cancelled.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The genuine full marked two-lower-root-face parametrization retains exactly the original first coordinate leg
and both original root-coface images. -/
theorem coneLowerLowerRootFaceIso_left {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 3))
    (h : j.castSucc < k) (hj : 0 < j) :
    (coneLowerLowerRootFaceIso.{u} j k h hj).hom ≫ coneLowerLowerRootFaceLeft j.castSucc k =
      coneRootCofaceImage (k.pred h.ne_zero)
        (lt_of_lt_of_le hj ((Fin.le_pred_iff h.ne_zero).mpr (Fin.castSucc_lt_iff_succ_le.mp h))) ≫
          (coneLowerRootFaceIso j.castSucc hj).hom := by
  have hp : 0 < k.pred h.ne_zero :=
    lt_of_lt_of_le hj ((Fin.le_pred_iff h.ne_zero).mpr (Fin.castSucc_lt_iff_succ_le.mp h))
  let e := coneLowerLowerRootFaceIso.{u} j k h hj
  let p := coneLowerRootFaceInclusion.{u} j.castSucc
  let a := coneRootCofaceImage.{u} (k.pred h.ne_zero) hp
  let f := coneDoubleCofaceEmbedding.{u} j k h
  let t := coneImage f.toOrderHom (⊥ : Vertex.{u} n) ≫
    eqToHom (congrArg (fun i : Vertex.{u} (n + 2) => coneWeight i) (coneDoubleCofaceEmbedding_root j k h hj))
  apply (cancel_mono p).mp
  have hl : (e.hom ≫ coneLowerLowerRootFaceLeft j.castSucc k) ≫ p = t :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => e.hom ≫ z) (coneLowerLowerRootFaceLeft_inclusion j.castSucc k)).trans
        (coneLowerLowerRootFaceIso_inclusion j k h hj))
  have hc : a ≫ coneRootCofaceImage j.castSucc hj = t :=
    coneRootCofaceImage_comp (k.pred h.ne_zero) hp j.castSucc hj
  have hr : (a ≫ (coneLowerRootFaceIso j.castSucc hj).hom) ≫ p = t :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => a ≫ z) (coneLowerRootFaceIso_rootImage j.castSucc hj)).trans hc)
  exact hl.trans hr.symm

/-- The genuine full marked two-lower-root-face parametrization retains exactly the original second coordinate leg
and the alternative same original double-coface image. -/
theorem coneLowerLowerRootFaceIso_right {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 3))
    (h : j.castSucc < k) (hj : 0 < j) :
    (coneLowerLowerRootFaceIso.{u} j k h hj).hom ≫ coneLowerLowerRootFaceRight j.castSucc k =
      coneRootCofaceImage j hj ≫
        (coneLowerRootFaceIso k ((show (0 : Fin (n + 3)) < j.castSucc from hj).trans h)).hom := by
  have hk : 0 < k := (show (0 : Fin (n + 3)) < j.castSucc from hj).trans h
  let e := coneLowerLowerRootFaceIso.{u} j k h hj
  let p := coneLowerRootFaceInclusion.{u} k
  let a := coneRootCofaceImage.{u} j hj
  let f := coneDoubleCofaceEmbedding.{u} j k h
  let g := (coneCofaceEmbedding.{u} k).toOrderHom.comp (coneCofaceEmbedding.{u} j).toOrderHom
  let hf := coneDoubleCofaceEmbedding_root.{u} j k h hj
  let hg := (congrArg (coneCofaceEmbedding.{u} k) (coneCofaceEmbedding_root j hj)).trans (coneCofaceEmbedding_root k hk)
  let t := coneImage f.toOrderHom (⊥ : Vertex.{u} n) ≫ eqToHom (congrArg (fun i : Vertex.{u} (n + 2) => coneWeight
    i) hf)
  apply (cancel_mono p).mp
  have hl : (e.hom ≫ coneLowerLowerRootFaceRight j.castSucc k) ≫ p = t :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => e.hom ≫ z) (coneLowerLowerRootFaceRight_inclusion j.castSucc k)).trans
        (coneLowerLowerRootFaceIso_inclusion j k h hj))
  have hg' : g = f.toOrderHom :=
    (congrArg (fun v : Vertex.{u} n ↪o Vertex.{u} (n + 2) => v.toOrderHom) (coneDoubleCofaceEmbedding_eq j k h)).symm
  have hc : a ≫ coneRootCofaceImage k hk = t :=
    (coneRootCofaceImage_comp j hj k hk).trans (coneRootConeImage_congr g f.toOrderHom hg hf hg')
  have hr : (a ≫ (coneLowerRootFaceIso k hk).hom) ≫ p = t :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => a ≫ z) (coneLowerRootFaceIso_rootImage k hk)).trans hc)
  exact hl.trans hr.symm

end SSet.Marked.CoherentWeight

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The whole original lower-root coordinate inverse reads exactly its genuine original coface unit after
precomposition by the original marked lower-face isomorphism. -/
theorem nativeLowerRootBoundaryInverse_coface {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : 0 < j) :
    (coneLowerRootFaceIso j hj).hom ≫ nativeLowerRootBoundaryInverse B σ j hj =
      nativeLowerCofaceRootSection B σ j ≫
        eqToHom (nativeLowerCofaceRootTarget B σ j hj (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))) := by
  let e := coneLowerRootFaceIso.{u} j hj
  let a := nativeLowerCofaceRootSection B σ j
  let b := eqToHom (nativeLowerCofaceRootTarget B σ j hj (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))))
  change e.hom ≫ ((e.inv ≫ a) ≫ b) = a ≫ b
  exact (congrArg (fun z => e.hom ≫ z) (Category.assoc _ _ _)).trans (e.hom_inv_id_assoc (a ≫ b))

/-- The two genuine original lower-coordinate inverse maps agree on the entire original marked lower/lower
intersection for every ordered positive original vertex pair, in the actual unchanged native boundary source. -/
theorem nativeLowerLowerRootInverse_condition (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (j : Fin (n + 2)) (k : Fin (n + 3)) (h : j.castSucc < k) (hj : 0 < j) :
    coneLowerLowerRootFaceLeft j.castSucc k ≫ nativeLowerRootBoundaryInverse B σ j.castSucc hj =
      coneLowerLowerRootFaceRight j.castSucc k ≫
        nativeLowerRootBoundaryInverse B σ k ((show (0 : Fin (n + 3)) < j.castSucc from hj).trans h) := by
  have hp : 0 < k.pred h.ne_zero :=
    lt_of_lt_of_le hj ((Fin.le_pred_iff h.ne_zero).mpr (Fin.castSucc_lt_iff_succ_le.mp h))
  have hk : 0 < k := (show (0 : Fin (n + 3)) < j.castSucc from hj).trans h
  let e := coneLowerLowerRootFaceIso.{u} j k h hj
  let a := coneRootCofaceImage.{u} (k.pred h.ne_zero) hp
  let b := coneRootCofaceImage.{u} j hj
  let u := nativeLowerCofaceRootSection B σ j.castSucc ≫
    eqToHom (nativeLowerCofaceRootTarget B σ j.castSucc hj (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))))
  let v := nativeLowerCofaceRootSection B σ k ≫
    eqToHom (nativeLowerCofaceRootTarget B σ k hk (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))))
  apply (cancel_epi e.hom).mp
  have hl : e.hom ≫ (coneLowerLowerRootFaceLeft j.castSucc k ≫ nativeLowerRootBoundaryInverse B σ j.castSucc hj) = a
    ≫ u :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ nativeLowerRootBoundaryInverse B σ j.castSucc hj) (coneLowerLowerRootFaceIso_left j k
        h hj)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z => a ≫ z) (nativeLowerRootBoundaryInverse_coface B σ j.castSucc hj))))
  have hr : e.hom ≫ (coneLowerLowerRootFaceRight j.castSucc k ≫ nativeLowerRootBoundaryInverse B σ k hk) = b ≫ v :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ nativeLowerRootBoundaryInverse B σ k hk) (coneLowerLowerRootFaceIso_right j k h
        hj)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z => b ≫ z) (nativeLowerRootBoundaryInverse_coface B σ k hk))))
  have hc : a ≫ u = b ≫ v := nativeLowerDoubleCofaceRoot_condition B n σ j k h hj
  exact hl.trans (hc.trans hr.symm)

end SSet.Marked
