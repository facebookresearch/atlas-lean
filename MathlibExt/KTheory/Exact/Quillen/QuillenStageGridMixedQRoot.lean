/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMixedZeroRoot
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridQEdgeValues

/-!
# Actual original mixed grid-root projection to the Quillen zero root

The original chosen left/central/right grid edges project respectively to
identity, EXACT generic Quillen zero edge, and identity. Their actual realized
path therefore has the original mapped-zero-to-selected-zero Q root. Every
map/root/time is retained; no root comparison is supplied by the caller.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial Topology ZeroObject

universe uC vC uD vD

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- Standard Waldhausen structure selected locally for the source exact category. -/
local instance originalMixedQRootWaldhausenC : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C
/-- Standard Waldhausen structure selected locally for the target exact category. -/
local instance originalMixedQRootWaldhausenD : WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

private theorem originalMixedMappedZero_q :
    (originalMixedGridMappedZeroLift F).q =
      ComposableArrows.mk₀ ((QuillenQ.map F).obj (⟨0⟩ : QuillenQ C)) := by
  rw [originalMixedGridMappedZeroLift_eq F,
    quillenStageGridLiftMap_obj_q, quillenStageGridZeroLift_q]
  apply ComposableArrows.ext₀
  rfl

private theorem originalMixedTargetZero_q :
    (originalMixedGridTargetZeroLift (D := D)).q = NQ.zeroVertex D := by
  rw [originalMixedGridTargetZeroLift_eq (D := D)]
  exact quillenStageGridZeroLift_q D

private theorem originalMixedSourceFace_q :
    (originalMixedGridZeroSource F).q =
      ComposableArrows.mk₀ ((QuillenQ.map F).obj (⟨0⟩ : QuillenQ C)) :=
  (originalMixedGridZeroSource_q F).trans (originalMixedMappedZero_q F)

private theorem originalMixedTargetFace_q :
    (originalMixedGridZeroTarget F).q = NQ.zeroVertex D :=
  (originalMixedGridZeroTarget_q F).trans (originalMixedTargetZero_q (D := D))

private def originalMixedLeftQEdge :
    (NQ D).Edge
      (ComposableArrows.mk₀ ((QuillenQ.map F).obj (⟨0⟩ : QuillenQ C)))
      (ComposableArrows.mk₀ ((QuillenQ.map F).obj (⟨0⟩ : QuillenQ C))) :=
  ((originalMixedGridZeroLeftEdge F).map (quillenStageGridToNQ (C := D))).ofEq
    ((quillenStageGridToNQ_diagonal_value D (op ⦋0⦌) _).trans (originalMixedMappedZero_q F))
    ((quillenStageGridToNQ_diagonal_value D (op ⦋0⦌) _).trans (originalMixedSourceFace_q F))

private def originalMixedCentralQEdge :
    (NQ D).Edge
      (ComposableArrows.mk₀ ((QuillenQ.map F).obj (⟨0⟩ : QuillenQ C))) (NQ.zeroVertex D) :=
  ((originalMixedGridZeroCentralEdge F).map (quillenStageGridToNQ (C := D))).ofEq
    ((quillenStageGridToNQ_diagonal_value D (op ⦋0⦌) _).trans (originalMixedSourceFace_q F))
    ((quillenStageGridToNQ_diagonal_value D (op ⦋0⦌) _).trans (originalMixedTargetFace_q F))

private def originalMixedRightQEdge : (NQ D).Edge (NQ.zeroVertex D) (NQ.zeroVertex D) :=
  ((originalMixedGridZeroRightEdge F).map (quillenStageGridToNQ (C := D))).ofEq
    ((quillenStageGridToNQ_diagonal_value D (op ⦋0⦌) _).trans (originalMixedTargetFace_q F))
    ((quillenStageGridToNQ_diagonal_value D (op ⦋0⦌) _).trans (originalMixedTargetZero_q (D := D)))

private theorem originalMixedLeftQEdge_eq :
    originalMixedLeftQEdge F = SSet.Edge.id (X := NQ D)
      (ComposableArrows.mk₀ ((QuillenQ.map F).obj (⟨0⟩ : QuillenQ C))) := by
  apply SSet.Edge.ext
  change ((originalMixedGridZeroLeftEdge F).map (quillenStageGridToNQ (C := D))).edge = _
  exact (originalMixedGridZeroLeftEdge_Q_value F).trans
    (congrArg (fun q => (SSet.Edge.id (X := NQ D) q).edge)
      (originalMixedMappedZero_q F))

private theorem originalMixedCentralQEdge_eq :
    originalMixedCentralQEdge F = NQFunctorZeroEdge F := by
  apply SSet.Edge.ext
  change ((originalMixedGridZeroCentralEdge F).map
    (quillenStageGridToNQ (C := D))).edge = (NQFunctorZeroEdge F).edge
  have hEdge : (originalMixedGridZeroCentralEdge F).edge =
      (ComposableArrows.mk₁ (𝟙 (originalMixedGridZeroLift F)) :
        (quillenStageGridDiagonal D).obj (op ⦋1⦌)) :=
    (originalMixedGridZeroCentralEdge_edge F).trans (originalMixedGridZeroCentralSimplex_eq F)
  have hProjected :
      (quillenStageGridToNQ (C := D)).app (op ⦋1⦌)
        (ComposableArrows.mk₁ (𝟙 (originalMixedGridZeroLift F))) =
          (NQFunctorZeroEdge F).edge :=
    (quillenStageGridIdentityOneSimplex_toNQ_value D (originalMixedGridZeroLift F)).trans
      ((originalMixedGridZeroLift_q F).trans (originalMixedGridZeroQEdge_eq F))
  exact (SSet.Edge.map_edge (originalMixedGridZeroCentralEdge F)
    (quillenStageGridToNQ (C := D))).trans
      ((congrArg (fun q : (quillenStageGridDiagonal D).obj (op ⦋1⦌) =>
        (quillenStageGridToNQ (C := D)).app (op ⦋1⦌) q) hEdge).trans hProjected)

private theorem originalMixedRightQEdge_eq : originalMixedRightQEdge F = SSet.Edge.id (NQ.zeroVertex D) := by
  apply SSet.Edge.ext
  change ((originalMixedGridZeroRightEdge F).map (quillenStageGridToNQ (C := D))).edge = _
  exact (originalMixedGridZeroRightEdge_Q_value F).trans
    (congrArg (fun q => (SSet.Edge.id q).edge) (originalMixedTargetFace_q F))

private def originalMixedQProjectionPath :
    Path
      (SSet.realizedVertex (ComposableArrows.mk₀ ((QuillenQ.map F).obj (⟨0⟩ : QuillenQ C))))
      (SSet.realizedVertex (NQ.zeroVertex D)) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedLeftQEdge F))).trans
    ((TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedCentralQEdge F))).trans
      (TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedRightQEdge F))))

private theorem originalMixedQProjectionPath_homotopic :
    (originalMixedQProjectionPath F).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath (NQFunctorZeroEdge F))) := by
  rw [originalMixedQProjectionPath, originalMixedLeftQEdge_eq,
    originalMixedCentralQEdge_eq, originalMixedRightQEdge_eq]
  let q0 := ComposableArrows.mk₀ ((QuillenQ.map F).obj (⟨0⟩ : QuillenQ C))
  let q1 := NQ.zeroVertex D
  let p := TopCat.pathEquiv (SSet.realizedEdgePath (NQFunctorZeroEdge F))
  have h0 := SSet.realizedEdgePath_id_homotopic (X := NQ D) q0
  have h1 := SSet.realizedEdgePath_id_homotopic (X := NQ D) q1
  exact (h0.hcomp (((Path.Homotopic.refl p).hcomp h1).trans
    (Path.Homotopic.trans_refl p))).trans (Path.Homotopic.refl_trans p)


private theorem originalProjectedEdgeValue
    {X Y : SSet.{max uD vD}} (f : X ⟶ Y)
    {a b : X.obj (op ⦋0⦌)} (e : X.Edge a b)
    {c d : Y.obj (op ⦋0⦌)} (e' : Y.Edge c d)
    (h : (e.map f).edge = e'.edge) (t : unitInterval) :
    (SSet.toTop.map f).hom (TopCat.pathEquiv (SSet.realizedEdgePath e) t) =
      TopCat.pathEquiv (SSet.realizedEdgePath e') t := by
  have hNat := SSet.realizedEdgePath_naturality_hom f e
  have hEq : (SSet.realizedEdgePath (e.map f)).hom = (SSet.realizedEdgePath e').hom :=
    (SSet.realizedEdgePath_hom (e.map f)).trans
      ((congrArg (fun q : Y.obj (op ⦋1⦌) =>
        SSet.stdSimplex.toTopObjIsoI.inv ≫ SSet.toTop.map (SSet.yonedaEquiv.symm q)) h).trans
          (SSet.realizedEdgePath_hom e').symm)
  exact (ConcreteCategory.congr_hom hNat (TopCat.I.homeomorph.symm t)).symm.trans
    (ConcreteCategory.congr_hom hEq (TopCat.I.homeomorph.symm t))

private theorem originalRawGridQProjectionCastValue :
    let f := (SSet.toTop.map (quillenStageGridToNQ (C := D))).hom
    let hs := (SSet.realizedVertex_naturality (quillenStageGridToNQ (C := D))
      (ComposableArrows.mk₀ (originalMixedGridMappedZeroLift F))).symm.trans
        (congrArg SSet.realizedVertex
          ((quillenStageGridToNQ_diagonal_value D (op ⦋0⦌) _).trans (originalMixedMappedZero_q F)))
    let ht := (SSet.realizedVertex_naturality (quillenStageGridToNQ (C := D))
      (ComposableArrows.mk₀ (originalMixedGridTargetZeroLift (D := D)))).symm.trans
        (congrArg SSet.realizedVertex
          ((quillenStageGridToNQ_diagonal_value D (op ⦋0⦌) _).trans (originalMixedTargetZero_q (D := D))))
    (((originalMixedGridZeroRawPath F).map f.continuous).cast hs.symm ht.symm) =
      originalMixedQProjectionPath F := by
  dsimp only
  apply Path.ext
  funext t
  let f := (SSet.toTop.map (quillenStageGridToNQ (C := D))).hom
  let pL := TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedGridZeroLeftEdge F))
  let pC := TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedGridZeroCentralEdge F))
  let pR := TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedGridZeroRightEdge F))
  let qL := TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedLeftQEdge F))
  let qC := TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedCentralQEdge F))
  let qR := TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedRightQEdge F))
  have hL (u : unitInterval) : f (pL u) = qL u :=
    originalProjectedEdgeValue.{uD, vD} (quillenStageGridToNQ (C := D))
      (originalMixedGridZeroLeftEdge F) (originalMixedLeftQEdge F) rfl u
  have hC (u : unitInterval) : f (pC u) = qC u :=
    originalProjectedEdgeValue.{uD, vD} (quillenStageGridToNQ (C := D))
      (originalMixedGridZeroCentralEdge F) (originalMixedCentralQEdge F) rfl u
  have hR (u : unitInterval) : f (pR u) = qR u :=
    originalProjectedEdgeValue.{uD, vD} (quillenStageGridToNQ (C := D))
      (originalMixedGridZeroRightEdge F) (originalMixedRightQEdge F) rfl u
  change f ((originalMixedGridZeroRawPath F).toContinuousMap.toFun t) =
    (qL.trans (qC.trans qR)).toContinuousMap.toFun t
  rw [originalMixedGridZeroRawPath_toContinuousMap F]
  change f ((pL.trans (pC.trans pR)).toContinuousMap.toFun t) =
    (qL.trans (qC.trans qR)).toContinuousMap.toFun t
  have hPL (u : unitInterval) :
      (pL.trans (pC.trans pR)).toContinuousMap.toFun u = _ :=
    Path.trans_apply pL (pC.trans pR) u
  have hQL (u : unitInterval) :
      (qL.trans (qC.trans qR)).toContinuousMap.toFun u = _ :=
    Path.trans_apply qL (qC.trans qR) u
  have hPC (u : unitInterval) : (pC.trans pR).toContinuousMap.toFun u = _ :=
    Path.trans_apply pC pR u
  have hQC (u : unitInterval) : (qC.trans qR).toContinuousMap.toFun u = _ :=
    Path.trans_apply qC qR u
  rw [hPL, hQL]
  split_ifs with ht
  · exact hL _
  · refine (congrArg f (hPC _)).trans (Eq.trans ?_ (hQC _).symm)
    split_ifs
    · exact hC _
    · exact hR _

/-- The ACTUAL original mixed grid zero-root projects to the SAME original
Quillen root, with both endpoints transported by their actual derived values.
No root comparison or alternative path is supplied by the caller. -/
theorem quillenStageGridDiagonalMixedZeroRoot_toNQ_homotopic :
    let f := (SSet.toTop.map (quillenStageGridToNQ (C := D))).hom
    let x := quillenStageGridDiagonalReal.basepoint C
    let hSource : f (quillenStageGridDiagonalRealMixedMap F x) =
        (NQRealFunctorWeaklyPointed F).hom (NQReal.basepoint C) :=
      (congrArg (fun M : C(quillenStageGridDiagonalReal C, NQReal D) => M x)
        (quillenStageGridToNQ_mixed_realization_square F)).trans (by
          simpa only [ContinuousMap.comp_apply, NQRealFunctorWeaklyPointed_hom] using
            congrArg (CategoryTheory.realizedNerveFunctorMap (QuillenQ.map F))
              (quillenStageGridToNQ_map_basepoint C))
    (((quillenStageGridDiagonalMixedZeroRoot F).map f.continuous).cast
      hSource.symm (quillenStageGridToNQ_map_basepoint D).symm).Homotopic
        (NQRealFunctorWeaklyPointed F).rootPath := by
  dsimp only
  obtain ⟨K⟩ := originalMixedQProjectionPath_homotopic F
  let hF := NQRealFunctorWeaklyPointed_basepoint_eq_vertex F
  let hD := NQReal.basepoint_eq_realizedVertex D
  have h := K.pathCast hF hD
  refine ⟨h.cast ?_ ?_⟩
  · apply Path.ext
    funext t
    have hRaw := originalRawGridQProjectionCastValue F
    have hValue := congrArg
      (fun p : Path
        (SSet.realizedVertex (ComposableArrows.mk₀ ((QuillenQ.map F).obj (⟨0⟩ : QuillenQ C))))
        (SSet.realizedVertex (NQ.zeroVertex D)) => p.toContinuousMap.toFun t) hRaw
    change (originalMixedQProjectionPath F).toContinuousMap.toFun t =
      (SSet.toTop.map (quillenStageGridToNQ (C := D))).hom
        ((quillenStageGridDiagonalMixedZeroRoot F).toContinuousMap.toFun t)
    rw [quillenStageGridDiagonalMixedZeroRoot_toContinuousMap F]
    exact hValue.symm
  · apply Path.ext
    funext t
    exact (NQRealFunctorWeaklyPointed_rootPath_apply F t).symm

end AlgebraicKTheory

end
