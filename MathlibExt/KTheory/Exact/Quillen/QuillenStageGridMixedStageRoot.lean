/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMixedZeroRoot
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenMixedKSpaceMap

/-!
# The actual original mixed grid root projects to its Stage root

All three EXACT selected grid edges have derived zero Stage off-diagonal
components. The original target Stage zero-connector homotopies telescope their
ordered paths to the ACTUAL mixed Stage zero edge, retaining the original
mapped-zero point and selected target zero. No root/triangle outcome is input.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial Topology

universe uC vC uD vD

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- Standard Waldhausen structure selected locally for the source exact category. -/
local instance originalMixedStageRootWaldhausenC : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C
/-- Standard Waldhausen structure selected locally for the target exact category. -/
local instance originalMixedStageRootWaldhausenD : WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

private theorem originalMixedMappedZero_toStage :
    (quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (originalMixedGridMappedZeroLift F)) =
      (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedMappedZeroVertex := by
  let q0 : (SSet.uliftFunctor.{max uD vD, max uC vC}.obj
      (quillenStageGridDiagonal C)).obj (op ⦋0⦌) :=
    ULift.up (quillenStageGridDiagonalZeroVertex (C := C))
  have h := congrArg
    (fun a : SSet.uliftFunctor.{max uD vD, max uC vC}.obj (quillenStageGridDiagonal C) ⟶
      SSet.uliftFunctor.{max uC vC, max uD vD}.obj (stageWeakDiagonal D) =>
        (a.app (op ⦋0⦌) q0).down)
    (quillenStageGridToStage_carrierLift_square F)
  change (quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
    ((quillenStageGridDiagonalMixedMap F).app (op ⦋0⦌) q0).down =
    ((CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedMap.app (op ⦋0⦌)
      (ULift.up ((quillenStageGridToStageWeakDiagonal (C := C)).app (op ⦋0⦌)
        (quillenStageGridDiagonalZeroVertex (C := C))))).down at h
  rw [quillenStageGridDiagonalMixedMap_app] at h
  change (quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
    ((quillenStageGridDiagonalZeroVertex (C := C)) ⋙ quillenStageGridLiftMap F ⦋0⦌) =
    ((CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedMap.app (op ⦋0⦌)
      (ULift.up ((quillenStageGridToStageWeakDiagonal (C := C)).app (op ⦋0⦌)
        (quillenStageGridDiagonalZeroVertex (C := C))))).down at h
  have hMapped : (quillenStageGridDiagonalZeroVertex (C := C)) ⋙
      quillenStageGridLiftMap F ⦋0⦌ =
        ComposableArrows.mk₀ (originalMixedGridMappedZeroLift F) := by
    rw [originalMixedGridMappedZeroLift_eq F]
    apply ComposableArrows.ext₀
    rfl
  rw [hMapped, quillenStageGridToStageWeakDiagonal_zeroVertex,
    (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedMap_zeroVertex] at h
  exact h

private theorem originalMixedTargetZero_toStage :
    (quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
      (ComposableArrows.mk₀ (originalMixedGridTargetZeroLift (D := D))) =
    stageWeakDiagonalZeroVertex D := by
  rw [originalMixedGridTargetZeroLift_eq (D := D)]
  exact quillenStageGridTargetZeroLift_toStage (D := D)

private def originalMixedLeftStageEdge :
    (stageWeakDiagonal D).Edge
      (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedMappedZeroVertex
      ((quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (originalMixedGridZeroSource F))) :=
  ((originalMixedGridZeroLeftEdge F).map (quillenStageGridToStageWeakDiagonal (C := D))).ofEq
    (originalMixedMappedZero_toStage F) rfl

private def originalMixedCentralStageEdge :
    (stageWeakDiagonal D).Edge
      ((quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (originalMixedGridZeroSource F)))
      ((quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (originalMixedGridZeroTarget F))) :=
  (originalMixedGridZeroCentralEdge F).map (quillenStageGridToStageWeakDiagonal (C := D))

private def originalMixedRightStageEdge :
    (stageWeakDiagonal D).Edge
      ((quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (originalMixedGridZeroTarget F))) (stageWeakDiagonalZeroVertex D) :=
  ((originalMixedGridZeroRightEdge F).map (quillenStageGridToStageWeakDiagonal (C := D))).ofEq
    rfl (originalMixedTargetZero_toStage (D := D))

private theorem originalMixedLeftStage_isZero :
    IsZero ((stageOneEval D).obj (ComposableArrows.left (originalMixedLeftStageEdge F).edge).obj) :=
  originalMixedGridZeroLeftEdge_Stage_isZero F
private theorem originalMixedCentralStage_isZero :
    IsZero ((stageOneEval D).obj (ComposableArrows.left (originalMixedCentralStageEdge F).edge).obj) :=
  originalMixedGridZeroCentralEdge_Stage_isZero F
private theorem originalMixedRightStage_isZero :
    IsZero ((stageOneEval D).obj (ComposableArrows.left (originalMixedRightStageEdge F).edge).obj) :=
  originalMixedGridZeroRightEdge_Stage_isZero F

private def originalMixedStageProjectionPath :
    Path (SSet.realizedVertex
      (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedMappedZeroVertex)
      (SSet.realizedVertex (stageWeakDiagonalZeroVertex D)) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedLeftStageEdge F))).trans
    ((TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedCentralStageEdge F))).trans
      (TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedRightStageEdge F))))

private theorem originalMixedStageProjectionPath_homotopic :
    (originalMixedStageProjectionPath F).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalMixedZeroEdge F (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F)))) := by
  let eL := originalMixedLeftStageEdge F
  let eC := originalMixedCentralStageEdge F
  let eR := originalMixedRightStageEdge F
  let e0 := stageWeakDiagonalMixedZeroEdge F (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F)
  let pL := TopCat.pathEquiv (SSet.realizedEdgePath eL)
  let pC := TopCat.pathEquiv (SSet.realizedEdgePath eC)
  let pR := TopCat.pathEquiv (SSet.realizedEdgePath eR)
  let p0 := TopCat.pathEquiv (SSet.realizedEdgePath e0)
  let xS := (quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
    (ComposableArrows.mk₀ (originalMixedGridZeroSource F))
  let xT := (quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
    (ComposableArrows.mk₀ (originalMixedGridZeroTarget F))
  let cM := TopCat.pathEquiv (SSet.realizedEdgePath
    (stageWeakDiagonalZeroToVertexEdge D
      ((CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedMappedZeroVertex)))
  let cS := TopCat.pathEquiv (SSet.realizedEdgePath
    (stageWeakDiagonalZeroToVertexEdge D xS))
  let cT := TopCat.pathEquiv (SSet.realizedEdgePath
    (stageWeakDiagonalZeroToVertexEdge D xT))
  let cZ := TopCat.pathEquiv (SSet.realizedEdgePath
    (stageWeakDiagonalZeroToVertexEdge D
      (stageWeakDiagonalZeroVertex D)))
  have hL : (pL.trans cS.symm).Homotopic cM.symm := by
    exact stageWeakDiagonalEdge_comp_zeroConnectorSymm_homotopic_of_isZero
      D eL (originalMixedLeftStage_isZero F)
  have hC : (pC.trans cT.symm).Homotopic cS.symm := by
    exact stageWeakDiagonalEdge_comp_zeroConnectorSymm_homotopic_of_isZero
      D eC (originalMixedCentralStage_isZero F)
  have hR : (pR.trans cZ.symm).Homotopic cT.symm := by
    exact stageWeakDiagonalEdge_comp_zeroConnectorSymm_homotopic_of_isZero
      D eR (originalMixedRightStage_isZero F)
  have hzero0 : IsZero ((stageOneEval D).obj
      (ComposableArrows.left e0.edge).obj) := by
    rw [stageWeakDiagonalMixedZeroEdge_edge]
    change IsZero ((mixedWaldhausenZeroEdgeWeak F
      (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F)).obj.obj.obj
        (interval (0 : Fin 2) 1 (by decide)))
    rw [mixedWaldhausenZeroEdgeWeak_diagram]
    exact mixedWaldhausenZeroEdgeDiagram_isZero F (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F)
      (interval (0 : Fin 2) 1 (by decide))
  have h0 : (p0.trans cZ.symm).Homotopic cM.symm := by
    exact stageWeakDiagonalEdge_comp_zeroConnectorSymm_homotopic_of_isZero
      D e0 hzero0
  have hLq := Path.Homotopic.Quotient.eq.mpr hL
  have hCq := Path.Homotopic.Quotient.eq.mpr hC
  have hRq := Path.Homotopic.Quotient.eq.mpr hR
  have h0q := Path.Homotopic.Quotient.eq.mpr h0
  simp only [Path.Homotopic.Quotient.mk_trans] at hLq hCq hRq h0q
  let m := SSet.realizedVertex
    ((CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedMappedZeroVertex)
  let s := SSet.realizedVertex xS
  let t := SSet.realizedVertex xT
  let z := SSet.realizedVertex (stageWeakDiagonalZeroVertex D)
  let qL : _root_.FundamentalGroupoid.mk m ⟶
      _root_.FundamentalGroupoid.mk s :=
    Path.Homotopic.Quotient.mk pL
  let qC : _root_.FundamentalGroupoid.mk s ⟶
      _root_.FundamentalGroupoid.mk t :=
    Path.Homotopic.Quotient.mk pC
  let qR : _root_.FundamentalGroupoid.mk t ⟶
      _root_.FundamentalGroupoid.mk z :=
    Path.Homotopic.Quotient.mk pR
  let q0 : _root_.FundamentalGroupoid.mk m ⟶
      _root_.FundamentalGroupoid.mk z :=
    Path.Homotopic.Quotient.mk p0
  let qM : _root_.FundamentalGroupoid.mk m ⟶
      _root_.FundamentalGroupoid.mk z :=
    Path.Homotopic.Quotient.mk cM.symm
  let qS : _root_.FundamentalGroupoid.mk s ⟶
      _root_.FundamentalGroupoid.mk z :=
    Path.Homotopic.Quotient.mk cS.symm
  let qT : _root_.FundamentalGroupoid.mk t ⟶
      _root_.FundamentalGroupoid.mk z :=
    Path.Homotopic.Quotient.mk cT.symm
  let qZ : _root_.FundamentalGroupoid.mk z ⟶
      _root_.FundamentalGroupoid.mk z :=
    Path.Homotopic.Quotient.mk cZ.symm
  change qL ≫ qS = qM at hLq
  change qC ≫ qT = qS at hCq
  change qR ≫ qZ = qT at hRq
  change q0 ≫ qZ = qM at h0q
  have hcat :
      (qL ≫ (qC ≫ qR)) ≫ qZ = q0 ≫ qZ := by
    calc
      _ = qL ≫ (qC ≫ (qR ≫ qZ)) := by
            simp only [Category.assoc]
      _ = qL ≫ (qC ≫ qT) := by rw [hRq]
      _ = qL ≫ qS := by rw [hCq]
      _ = qM := hLq
      _ = q0 ≫ qZ := h0q.symm
  have hbare :
      qL ≫ (qC ≫ qR) = q0 :=
    (cancel_mono qZ).mp hcat
  change (pL.trans (pC.trans pR)).Homotopic p0
  apply Path.Homotopic.Quotient.eq.mp
  simpa only [qL, qC, qR, q0,
    Path.Homotopic.Quotient.mk_trans,
    _root_.FundamentalGroupoid.comp_eq] using hbare




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

private theorem originalRawGridStageProjectionCastValue :
    let f := (SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := D))).hom
    let hs := (SSet.realizedVertex_naturality (quillenStageGridToStageWeakDiagonal (C := D))
      (ComposableArrows.mk₀ (originalMixedGridMappedZeroLift F))).symm.trans
        (congrArg SSet.realizedVertex (originalMixedMappedZero_toStage F))
    let ht := (SSet.realizedVertex_naturality (quillenStageGridToStageWeakDiagonal (C := D))
      (ComposableArrows.mk₀ (originalMixedGridTargetZeroLift (D := D)))).symm.trans
        (congrArg SSet.realizedVertex (originalMixedTargetZero_toStage (D := D)))
    (((originalMixedGridZeroRawPath F).map f.continuous).cast hs.symm ht.symm) =
      originalMixedStageProjectionPath F := by
  dsimp only
  apply Path.ext
  funext t
  let f := (SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := D))).hom
  let pL := TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedGridZeroLeftEdge F))
  let pC := TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedGridZeroCentralEdge F))
  let pR := TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedGridZeroRightEdge F))
  let qL := TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedLeftStageEdge F))
  let qC := TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedCentralStageEdge F))
  let qR := TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedRightStageEdge F))
  have hL (u : unitInterval) : f (pL u) = qL u :=
    originalProjectedEdgeValue.{uD, vD} (quillenStageGridToStageWeakDiagonal (C := D))
      (originalMixedGridZeroLeftEdge F) (originalMixedLeftStageEdge F) rfl u
  have hC (u : unitInterval) : f (pC u) = qC u :=
    originalProjectedEdgeValue.{uD, vD} (quillenStageGridToStageWeakDiagonal (C := D))
      (originalMixedGridZeroCentralEdge F) (originalMixedCentralStageEdge F) rfl u
  have hR (u : unitInterval) : f (pR u) = qR u :=
    originalProjectedEdgeValue.{uD, vD} (quillenStageGridToStageWeakDiagonal (C := D))
      (originalMixedGridZeroRightEdge F) (originalMixedRightStageEdge F) rfl u
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


/-- The mixed grid root projects to the original stage map root through the
complete comparison square in independent category universes and original edge paths. -/
theorem quillenStageGridDiagonalMixedZeroRoot_toStage_homotopic :
    let f := (SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := D))).hom
    let x := quillenStageGridDiagonalReal.basepoint C
    let hSource : f (quillenStageGridDiagonalRealMixedMap F x) =
        (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap
          (stageWeakDiagonalReal.basepoint C) :=
      (congrArg (fun M : C(quillenStageGridDiagonalReal C, stageWeakDiagonalReal D) => M x)
        (quillenStageGridToStage_mixed_realization_square F)).trans
          (congrArg (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap
            ((quillenStageGridToStageWeakDiagonal_realizedZeroVertex (C := C)).trans
              (stageWeakDiagonalReal.basepoint_eq_realizedVertex C).symm))
    let hTarget : f (quillenStageGridDiagonalReal.basepoint D) =
        stageWeakDiagonalReal.basepoint D :=
      (quillenStageGridToStageWeakDiagonal_realizedZeroVertex (C := D)).trans
        (stageWeakDiagonalReal.basepoint_eq_realizedVertex D).symm
    (((quillenStageGridDiagonalMixedZeroRoot F).map f.continuous).cast
      hSource.symm hTarget.symm).Homotopic
        (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedRootPath := by
  dsimp only
  obtain ⟨K⟩ := originalMixedStageProjectionPath_homotopic F
  let hF := (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap_basepoint
  let hD := stageWeakDiagonalReal.basepoint_eq_realizedVertex D
  have h := K.pathCast hF hD
  refine ⟨h.cast ?_ ?_⟩
  · apply Path.ext
    funext t
    have hRaw := originalRawGridStageProjectionCastValue F
    have hValue := congrArg (fun p : Path
      (SSet.realizedVertex
        (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedMappedZeroVertex)
      (SSet.realizedVertex (stageWeakDiagonalZeroVertex D)) => p.toContinuousMap.toFun t) hRaw
    change (originalMixedStageProjectionPath F).toContinuousMap.toFun t =
      (SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := D))).hom
        ((quillenStageGridDiagonalMixedZeroRoot F).toContinuousMap.toFun t)
    rw [quillenStageGridDiagonalMixedZeroRoot_toContinuousMap F]
    exact hValue.symm
  · apply Path.ext
    funext t
    exact (congrArg (fun M : C(unitInterval, stageWeakDiagonalReal D) => M t)
      (CategoryTheory.Functor.IsWaldhausenExact.stageWeakDiagonalMixedRootPath_toContinuousMap
        (CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory F))).symm

end AlgebraicKTheory

end
