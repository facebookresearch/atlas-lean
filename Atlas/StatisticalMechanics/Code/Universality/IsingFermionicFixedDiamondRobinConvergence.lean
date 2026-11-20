/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicFullSquareBoundaryProjectionAnalyticCollar
import Code.Universality.IsingFermionicEndpointRadialPointGreen











namespace StatMech.Universality

open Filter Metric Set
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm



theorem tendsto_fixedDiamond_endpointRadialHarmonic :
    Tendsto (fun k =>
      (harmonic (3 * isingFermionicProjectionPolynomialSide k + 1) : Real) /
        (isingFermionicProjectionPolynomialSide k : Real))
      atTop (nhds 0) := by
  let q : Nat -> Nat := fun k =>
    isingFermionicProjectionPolynomialSide k - 1
  have hq : Tendsto q atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a hab => ?_⟩
    dsimp [q, isingFermionicProjectionPolynomialSide,
      isingFermionicPolynomialSide]
    have hpow : b + 1 <= (a + 2) ^ 5 := by
      calc
        b + 1 <= a + 1 := Nat.add_le_add_right hab 1
        _ <= a + 2 := by omega
        _ <= (a + 2) ^ 5 := Nat.le_pow (by norm_num)
    omega
  have hcomp := tendsto_endpointRadialHarmonic_div_natCast_succ.comp hq
  convert hcomp using 1
  funext k
  have hpos : 0 < isingFermionicProjectionPolynomialSide k :=
    isingFermionicProjectionPolynomialSide_pos k
  simp only [Function.comp_apply, q, Nat.sub_add_cancel hpos]




theorem fixedDiamond_global_side_traces_inconsistent
    {Phi : Complex -> Complex}
    (hleftTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
      isingFermionicFixedDiamondLeftSide)
    (hfreeTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
      isingFermionicFixedDiamondFreeSides) : False := by
  have hleft : (-2 : Complex) ∈ isingFermionicFixedDiamondLeftSide := by
    simp [isingFermionicFixedDiamondLeftSide]
  have hfree : (-2 : Complex) ∈ isingFermionicFixedDiamondFreeSides := by
    simp [isingFermionicFixedDiamondFreeSides]
  exact zero_ne_one ((hleftTrace hleft).symm.trans (hfreeTrace hfree))



def isingFermionicFixedDiamondOrdinaryLowerTraceCarrier : Set Complex :=
  {z |
    (∃ k x,
      fkIsingSquareFullVertexFixedBoundary
          (isingFermionicProjectionPolynomialSide k) x ∧
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) x) ∧
      z = fullSquareVertexBoundaryProjection
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) x) ∨
    (∃ k c,
      Not (fkIsingSquareFullFaceFixedBoundary
        (isingFermionicProjectionPolynomialSide k) c) ∧
      0 < fkIsingSquareFullFaceGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) c ∧
      Not (faceMarkedEndpointLayer
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialRadius k) (some c)) ∧
      z = fullSquareFaceFreeBoundaryProjection
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) c)}


def isingFermionicFixedDiamondOrdinaryUpperTraceCarrier : Set Complex :=
  {z |
    (∃ k c,
      fkIsingSquareFullFaceFixedBoundary
          (isingFermionicProjectionPolynomialSide k) c ∧
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) c) ∧
      z = fullSquareFaceFixedBoundaryProjection
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) c) ∨
    (∃ k x,
      Not (fkIsingSquareFullVertexFixedBoundary
        (isingFermionicProjectionPolynomialSide k) x) ∧
      0 < fkIsingSquareFullVertexGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) x ∧
      Not (vertexMarkedEndpointLayer
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialRadius k) (some x)) ∧
      z = fullSquareVertexFreeBoundaryProjection
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) x)}




noncomputable def fixedDiamondLayerIncrementDataOfLipschitz
    {Phi : Complex -> Complex} (L : NNReal)
    (hPhi : LipschitzOnWith L (fun z => (Phi z).im)
      isingFermionicFixedClosedDiamond) :
    PhysicalEndpointLayerIncrementData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius :=
  PhysicalEndpointLayerIncrementData.ofLipschitzOn
    isingFermionicFixedClosedDiamond L hPhi
    isingFermionicFixedDiamondMesh_nonneg
    (fun k x _hfixed _hghost _hendpoint =>
      ⟨fullSquareScaledVertexEmbedding_mem_fixedClosedDiamond k x,
        fun y _hxy =>
          fullSquareScaledVertexEmbedding_mem_fixedClosedDiamond k y⟩)
    (fun k c _hfixed _hghost _hendpoint =>
      ⟨fullSquareScaledFaceEmbedding_mem_fixedClosedDiamond k c,
        fun d _hcd =>
          fullSquareScaledFaceEmbedding_mem_fixedClosedDiamond k d⟩)




theorem fixedDiamond_incidence_im_mismatch_le
    {Phi : Complex -> Complex} (L : NNReal)
    (hPhi : LipschitzOnWith L (fun z => (Phi z).im)
      isingFermionicFixedClosedDiamond)
    (k : Nat)
    (e : FKIsingSquareInteriorRadialIncidence
      (isingFermionicProjectionPolynomialSide k)
      (isingFermionicProjectionPolynomialSide_pos k)) :
    |(Phi (fullSquareScaledFaceEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k)
        (fkIsingSquareFullFaceOfRadialIncidence
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialSide_pos k) e))).im -
      (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k)
        (fkIsingSquareInteriorRadialEndpoint
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialSide_pos k) e))).im| <=
      (L : Real) * isingFermionicFixedDiamondMesh k := by
  let c := fkIsingSquareFullFaceOfRadialIncidence
    (isingFermionicProjectionPolynomialSide k)
    (isingFermionicProjectionPolynomialSide_pos k) e
  let x := fkIsingSquareInteriorRadialEndpoint
    (isingFermionicProjectionPolynomialSide k)
    (isingFermionicProjectionPolynomialSide_pos k) e
  rw [← Real.dist_eq]
  calc
    dist
        (Phi (fullSquareScaledFaceEmbedding
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k) c)).im
        (Phi (fullSquareScaledVertexEmbedding
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k) x)).im <=
        L * dist
          (fullSquareScaledFaceEmbedding
            (isingFermionicProjectionPolynomialSide k)
            (isingFermionicFixedDiamondMesh k) c)
          (fullSquareScaledVertexEmbedding
            (isingFermionicProjectionPolynomialSide k)
            (isingFermionicFixedDiamondMesh k) x) :=
      hPhi.dist_le_mul _
        (fullSquareScaledFaceEmbedding_mem_fixedClosedDiamond k c) _
        (fullSquareScaledVertexEmbedding_mem_fixedClosedDiamond k x)
    _ <= L * isingFermionicFixedDiamondMesh k := by
      gcongr
      exact fullSquareScaledEmbedding_incidenceDistance
        isingFermionicProjectionPolynomialSide
        isingFermionicProjectionPolynomialSide_pos
        isingFermionicFixedDiamondMesh
        isingFermionicFixedDiamondMesh_nonneg k e




theorem primitive_convergence_away_fixedDiamond_of_analyticCollar_lipschitz
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointFourthOrderBulkData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (L : NNReal)
    (hPhiLip : LipschitzOnWith L (fun z => (Phi z).im)
      isingFermionicFixedClosedDiamond)
    (U : Set Complex)
    (hPhi : AnalyticOnNhd Complex Phi U)
    (hrangeU : Set.MapsTo Phi U isingFermionicClosedUnitStrip)
    (hcollar : forall k c,
      c ∈ fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
          (isingFermionicProjectionPolynomialRadius k) ->
        ball c (isingFermionicFixedDiamondEndpointCollar k) ⊆ U)
    (hlowerTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
      isingFermionicFixedDiamondOrdinaryLowerTraceCarrier)
    (hupperTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
      isingFermionicFixedDiamondOrdinaryUpperTraceCarrier)
    (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond
      isingFermionicClosedUnitStrip) :
    forall eta : Real, 0 < eta -> Filter.Eventually (fun k =>
      forall e : FKIsingSquareInteriorRadialIncidence
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialSide_pos k),
        PhysicalProjectionPolynomialEndpointSafe k e ->
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicProjectionPolynomialSide k)
                (isingFermionicFixedDiamondMesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicProjectionPolynomialSide k)
                  (isingFermionicProjectionPolynomialSide_pos k) e))).im| < eta /\
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicProjectionPolynomialSide k)
                (isingFermionicFixedDiamondMesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicProjectionPolynomialSide k)
                  (isingFermionicProjectionPolynomialSide_pos k) e))).im| < eta)
      atTop := by
  let Hlayer := fixedDiamondLayerIncrementDataOfLipschitz L hPhiLip
  have hcarrierLip : forall k,
      LipschitzOnWith
        (isingFermionicFixedDiamondEndpointLipschitzConstant 8 k)
        (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
          (isingFermionicProjectionPolynomialRadius k)) := by
    intro k
    let K := fullSquareOrdinaryBoundaryProjectionCarrier
      (isingFermionicProjectionPolynomialSide k)
      (isingFermionicFixedDiamondMesh k)
      (isingFermionicProjectionPolynomialRadius k)
    have hLip := isingFermionic_unitStrip_lipschitzOn_carrier_of_balls
      Phi K (isingFermionicFixedDiamondEndpointCollar k)
      (isingFermionicFixedDiamondEndpointCollar_pos k)
      (fun c hc => hPhi.differentiableOn.mono (hcollar k c hc))
      (fun c hc z hz => hrangeU (hcollar k c hc hz))
      (fun z hz => hrangeU (hcollar k z hz
        (Metric.mem_ball_self
          (isingFermionicFixedDiamondEndpointCollar_pos k))))
    have hconstant :
        isingFermionicFixedDiamondEndpointLipschitzConstant 8 k =
          (⟨8 / isingFermionicFixedDiamondEndpointCollar k,
            (div_pos (by norm_num)
              (isingFermionicFixedDiamondEndpointCollar_pos k)).le⟩ : NNReal) := by
      ext
      exact isingFermionicFixedDiamondEndpointLipschitzConstant_eight_eq k
    rw [hconstant]
    exact hLip
  let H :=
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondOrdinaryTracesAndRangeWith
      Hfourth Hlayer
      (isingFermionicFixedDiamondEndpointLipschitzConstant 8)
      hcarrierLip
      (fun k x hfixed hghost => hlowerTrace
        (Or.inl ⟨k, x, hfixed, hghost, rfl⟩))
      (fun k c hfixed hghost => hupperTrace
        (Or.inl ⟨k, c, hfixed, hghost, rfl⟩))
      (fun k x hfixed hghost hendpoint => hupperTrace
        (Or.inr ⟨k, x, hfixed, hghost, hendpoint, rfl⟩))
      (fun k c hfixed hghost hendpoint => hlowerTrace
        (Or.inr ⟨k, c, hfixed, hghost, hendpoint, rfl⟩))
      (PhysicalEndpointLocalizedMarkedClampedRobinInputs.fixedDiamondRanges
        hrange).1
      (PhysicalEndpointLocalizedMarkedClampedRobinInputs.fixedDiamondRanges
        hrange).2
      (tendsto_isingFermionicFixedDiamondEndpointLipschitz_mul_mesh 8)
  apply H.primitive_convergence_away_fixedDiamond
    (fun k => (L : Real) * isingFermionicFixedDiamondMesh k)
  · intro k
    exact mul_nonneg L.2 (isingFermionicFixedDiamondMesh_nonneg k)
  · intro k e _hsafe
    exact fixedDiamond_incidence_im_mismatch_le L hPhiLip k e
  · simpa using
      tendsto_const_nhds.mul tendsto_isingFermionicFixedDiamondMesh

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
