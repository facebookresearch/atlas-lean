/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicMarkedEndpointInputAssembly
import Code.Universality.IsingFermionicEndpointAnalyticAssembly









namespace StatMech.Universality

open Filter
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm


structure PhysicalEndpointVariableFourthOrderBulkData
    (N : Nat -> Nat) (Phi : Complex -> Complex)
    (mesh : Nat -> Real) (radius : Nat -> Nat) where
  boundOne : Nat -> Real
  boundTwo : Nat -> Real
  boundSum_nonneg : forall k, 0 <= boundOne k + boundTwo k
  vertex : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      LocalDiagonalFourthOrderAnalyticData Phi
        (fullSquareScaledVertexEmbedding (N k) (mesh k) x)
        (mesh k) (boundOne k) (boundTwo k)
  face : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      LocalDiagonalFourthOrderAnalyticData Phi
        (fullSquareScaledFaceEmbedding (N k) (mesh k) c)
        (mesh k) (boundOne k) (boundTwo k)



noncomputable def
    PhysicalEndpointVariableFourthOrderBulkData.ofAnalyticTensorNormOnSegments
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (U : Nat -> Set Complex) (hU : forall k, IsOpen (U k))
    (hPhi : forall k, AnalyticOnNhd Complex Phi (U k))
    (M : Nat -> NNReal)
    (htensor : forall k w, w ∈ U k ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M k)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
      Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (mesh k)) (U k) /\
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (-mesh k)) (U k) /\
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (mesh k)) (U k) /\
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (-mesh k)) (U k))
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
      Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (mesh k)) (U k) /\
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (-mesh k)) (U k) /\
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (mesh k)) (U k) /\
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (-mesh k)) (U k)) :
    PhysicalEndpointVariableFourthOrderBulkData N Phi mesh radius where
  boundOne k := 4 * (M k : Real)
  boundTwo k := 4 * (M k : Real)
  boundSum_nonneg k := by positivity
  vertex k x hfixed hghost hendpoint := by
    obtain ⟨hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hvertex k x hfixed hghost hendpoint
    exact LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
      (U k) (hU k) (hPhi k) (M k) (htensor k)
      hpositiveOne hnegativeOne hpositiveTwo hnegativeTwo
  face k c hfixed hghost hendpoint := by
    obtain ⟨hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hface k c hfixed hghost hendpoint
    exact LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
      (U k) (hU k) (hPhi k) (M k) (htensor k)
      hpositiveOne hnegativeOne hpositiveTwo hnegativeTwo

theorem PhysicalEndpointVariableFourthOrderBulkData.vertexLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointVariableFourthOrderBulkData N Phi mesh radius)
    (k : Nat) (x : FKIsingSquareFullVertexNode (N k))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0)
    (hendpoint : Not (vertexMarkedEndpointLayer
      (N k) (radius k) (some x))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
      (fun y => (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) y)).im) x| <=
        (H.boundOne k + H.boundTwo k) * |mesh k| ^ 4 / 12 := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareVertex_bulk_directions (N k) x hfixed hghost
  rw [fullSquareScaledVertex_sampledLaplacian_eq_stencil
    (N k) (mesh k) (fun z => (Phi z).im) x
      heast hnorth hwest hsouth]
  exact (H.vertex k x hfixed hghost hendpoint).stencil

theorem PhysicalEndpointVariableFourthOrderBulkData.faceLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointVariableFourthOrderBulkData N Phi mesh radius)
    (k : Nat) (c : FKIsingSquareFullFaceNode (N k))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0)
    (hendpoint : Not (faceMarkedEndpointLayer
      (N k) (radius k) (some c))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
      (fun d => (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) d)).im) c| <=
        (H.boundOne k + H.boundTwo k) * |mesh k| ^ 4 / 12 := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareFace_bulk_coordinates (N k) c hfixed hghost
  rw [fullSquareScaledFace_sampledLaplacian_eq_stencil
    (N k) (mesh k) (fun z => (Phi z).im) c
      heast hnorth hwest hsouth]
  exact (H.face k c hfixed hghost hendpoint).stencil



structure PhysicalEndpointVariableLayerIncrementData
    (N : Nat -> Nat) (Phi : Complex -> Complex)
    (mesh : Nat -> Real) (radius : Nat -> Nat) where
  constant : Nat -> NNReal
  vertex : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
    forall y, (fkIsingSquareFullVertexGraph (N k)).Adj x y ->
      |(Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im -
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| <=
          constant k * mesh k
  face : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
    forall d, (fkIsingSquareFullFaceGraph (N k)).Adj c d ->
      |(Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im -
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im| <=
          constant k * mesh k



noncomputable def PhysicalEndpointVariableLayerIncrementData.ofLipschitzOn
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (S : Nat -> Set Complex) (L : Nat -> NNReal)
    (hPhi : forall k,
      LipschitzOnWith (L k) (fun z => (Phi z).im) (S k))
    (hmesh : forall k, 0 <= mesh k)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ S k /\
          forall y, (fkIsingSquareFullVertexGraph (N k)).Adj x y ->
            fullSquareScaledVertexEmbedding (N k) (mesh k) y ∈ S k)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ S k /\
          forall d, (fkIsingSquareFullFaceGraph (N k)).Adj c d ->
            fullSquareScaledFaceEmbedding (N k) (mesh k) d ∈ S k) :
    PhysicalEndpointVariableLayerIncrementData N Phi mesh radius where
  constant k := 2 * L k
  vertex k x hfixed hghost hendpoint y hxy := by
    obtain ⟨hx, hy⟩ := hvertex k x hfixed hghost hendpoint
    rw [← Real.dist_eq]
    calc
      dist
          (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im
          (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <=
          L k * dist
            (fullSquareScaledVertexEmbedding (N k) (mesh k) y)
            (fullSquareScaledVertexEmbedding (N k) (mesh k) x) :=
        (hPhi k).dist_le_mul _ (hy y hxy) _ hx
      _ <= L k * (2 * |mesh k|) := by
        gcongr
        exact fullSquareScaledVertexEmbedding_dist_le_two_abs
          (N k) (mesh k) x y hxy
      _ = (2 * L k : NNReal) * mesh k := by
        rw [abs_of_nonneg (hmesh k)]
        norm_num
        ring
  face k c hfixed hghost hendpoint d hcd := by
    obtain ⟨hc, hd⟩ := hface k c hfixed hghost hendpoint
    rw [← Real.dist_eq]
    calc
      dist
          (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im
          (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <=
          L k * dist
            (fullSquareScaledFaceEmbedding (N k) (mesh k) d)
            (fullSquareScaledFaceEmbedding (N k) (mesh k) c) :=
        (hPhi k).dist_le_mul _ (hd d hcd) _ hc
      _ <= L k * (2 * |mesh k|) := by
        gcongr
        exact fullSquareScaledFaceEmbedding_dist_le_two_abs
          (N k) (mesh k) c d hcd
      _ = (2 * L k : NNReal) * mesh k := by
        rw [abs_of_nonneg (hmesh k)]
        norm_num
        ring

theorem PhysicalEndpointVariableLayerIncrementData.vertexLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointVariableLayerIncrementData N Phi mesh radius)
    (hmesh : forall k, 0 <= mesh k) (k : Nat)
    (x : FKIsingSquareFullVertexNode (N k))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
    (hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x)
    (hendpoint : Not (vertexMarkedEndpointLayer
      (N k) (radius k) (some x))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
      (fun y => (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) y)).im) x| <= 4 * H.constant k * mesh k := by
  have hbound := isingFiniteGraphLaplacian_abs_le_four_mul
    (fkIsingSquareFullVertexGraph (N k))
    (fun y => (Phi (fullSquareScaledVertexEmbedding
      (N k) (mesh k) y)).im) x (H.constant k * mesh k)
    (mul_nonneg (H.constant k).2 (hmesh k))
    (fullVertex_neighbor_card_le_four (N k) x)
    (H.vertex k x hfixed hghost hendpoint)
  simpa [mul_assoc] using hbound

theorem PhysicalEndpointVariableLayerIncrementData.faceLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointVariableLayerIncrementData N Phi mesh radius)
    (hmesh : forall k, 0 <= mesh k) (k : Nat)
    (c : FKIsingSquareFullFaceNode (N k))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
    (hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c)
    (hendpoint : Not (faceMarkedEndpointLayer
      (N k) (radius k) (some c))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
      (fun d => (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) d)).im) c| <= 4 * H.constant k * mesh k := by
  have hbound := isingFiniteGraphLaplacian_abs_le_four_mul
    (fkIsingSquareFullFaceGraph (N k))
    (fun d => (Phi (fullSquareScaledFaceEmbedding
      (N k) (mesh k) d)).im) c (H.constant k * mesh k)
    (mul_nonneg (H.constant k).2 (hmesh k))
    (fullFace_neighbor_card_le_four (N k) c)
    (H.face k c hfixed hghost hendpoint)
  simpa [mul_assoc] using hbound




theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofVariableFourthOrderLayerTraceAndRange
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    {traceRate : Nat -> Real}
    (Hfourth : PhysicalEndpointVariableFourthOrderBulkData N Phi mesh radius)
    (Hlayer : PhysicalEndpointVariableLayerIncrementData N Phi mesh radius)
    (Htrace : PhysicalEndpointOrdinaryTraceData N Phi mesh radius traceRate)
    (hvertexRadius : forall k, 0 < radius k)
    (hfaceRadius : forall k, 2 <= radius k)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
    (hscaledFourth_tendsto : Tendsto (fun k =>
      ((Hfourth.boundOne k + Hfourth.boundTwo k) * |mesh k| ^ 4 / 12) *
        (N k : Real) ^ 2) atTop (nhds 0))
    (hlayer_tendsto : Tendsto (fun k =>
      (Hlayer.constant k : Real) * mesh k) atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius
      traceRate
      (fun k =>
        (Hfourth.boundOne k + Hfourth.boundTwo k) * |mesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant k) * mesh k +
        (3 * isingFermionicGhostCoefficient) * traceRate k)
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  apply PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofSampledResiduals
    hvertexRadius hfaceRadius
  · exact Htrace.trace_nonneg
  · intro k
    exact div_nonneg
      (mul_nonneg (Hfourth.boundSum_nonneg k)
        (pow_nonneg (abs_nonneg _) 4))
      (by norm_num)
  · intro k
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Hlayer.constant k).2)
        (hmesh_nonneg k))
      (mul_nonneg
        (mul_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le)
        (Htrace.trace_nonneg k))
  · intro _
    nlinarith [isingFermionicGhostCoefficient_pos.le]
  · exact Htrace.vertexFixed
  · exact Htrace.faceFixed
  · intro k x hfixed hghost hendpoint
    have htarget : vertexSampledImaginaryTarget (N k)
        (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi =
      isingFiniteGhostExtension 1
        (fun y => (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget, vertexGhostConductance, isingFiniteGhostLaplacian_some]
    simpa [isingFermionicGhostRate, hghost] using
      Hfourth.vertexLaplacian k x hfixed hghost hendpoint
  · intro k c hfixed hghost hendpoint
    have htarget : faceSampledImaginaryTarget (N k)
        (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi =
      isingFiniteGhostExtension 0
        (fun d => (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget, faceGhostConductance, isingFiniteGhostLaplacian_some]
    simpa [isingFermionicGhostRate, hghost] using
      Hfourth.faceLaplacian k c hfixed hghost hendpoint
  · intro k x hfixed hghost hendpoint
    have htarget : vertexSampledImaginaryTarget (N k)
        (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi =
      isingFiniteGhostExtension 1
        (fun y => (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget, vertexGhostConductance, isingFiniteGhostLaplacian_some]
    have hgraph := Hlayer.vertexLaplacian hmesh_nonneg
      k x hfixed hghost hendpoint
    have hrate0 := isingFermionicGhostRate_nonneg
      (fkIsingSquareFullVertexGhostMultiplicity (N k)) x
    have hrate := vertexGhostRate_le_threeCoefficient (N k) x
    calc
      |_ + _| <= |isingFiniteGraphLaplacian
          (fkIsingSquareFullVertexGraph (N k))
          (fun y => (Phi (fullSquareScaledVertexEmbedding
            (N k) (mesh k) y)).im) x| +
        |isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity (N k)) x *
            (1 - (Phi (fullSquareScaledVertexEmbedding
              (N k) (mesh k) x)).im)| := abs_add_le _ _
      _ <= 4 * Hlayer.constant k * mesh k +
          (3 * isingFermionicGhostCoefficient) * traceRate k := by
        rw [abs_mul, abs_of_nonneg hrate0]
        exact add_le_add hgraph
          (mul_le_mul hrate (Htrace.vertexFree k x hfixed hghost hendpoint)
            (abs_nonneg _)
            (mul_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le))
  · intro k c hfixed hghost hendpoint
    have htarget : faceSampledImaginaryTarget (N k)
        (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi =
      isingFiniteGhostExtension 0
        (fun d => (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget, faceGhostConductance, isingFiniteGhostLaplacian_some]
    have hgraph := Hlayer.faceLaplacian hmesh_nonneg
      k c hfixed hghost hendpoint
    have hrate0 := isingFermionicGhostRate_nonneg
      (fkIsingSquareFullFaceGhostMultiplicity (N k)) c
    have hrate : isingFermionicGhostRate
        (fkIsingSquareFullFaceGhostMultiplicity (N k)) c <=
          3 * isingFermionicGhostCoefficient := by
      have h := faceGhostRate_le_coefficient (N k) c
      nlinarith [isingFermionicGhostCoefficient_pos.le]
    calc
      |_ + _| <= |isingFiniteGraphLaplacian
          (fkIsingSquareFullFaceGraph (N k))
          (fun d => (Phi (fullSquareScaledFaceEmbedding
            (N k) (mesh k) d)).im) c| +
        |isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity (N k)) c *
            (0 - (Phi (fullSquareScaledFaceEmbedding
              (N k) (mesh k) c)).im)| := abs_add_le _ _
      _ <= 4 * Hlayer.constant k * mesh k +
          (3 * isingFermionicGhostCoefficient) * traceRate k := by
        rw [abs_mul, abs_of_nonneg hrate0]
        exact add_le_add hgraph
          (mul_le_mul hrate (Htrace.faceFree k c hfixed hghost hendpoint)
            (abs_nonneg _)
            (mul_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le))
  · intro k x _hfixed _hendpoint
    exact vertexMarkedEndpointClamped_weightedLaplacian_le_of_unitRange
      (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi
      (hvertexRange k) x
  · intro k c _hfixed _hendpoint
    exact faceMarkedEndpointClamped_weightedLaplacian_le_of_unitRange
      (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi
      (hfaceRange k) c
  · exact Htrace.trace_tendsto
  · exact hscaledFourth_tendsto
  · have hmeshPart : Tendsto
        (fun k => (4 * (Hlayer.constant k : Real)) * mesh k)
        atTop (nhds 0) := by
      simpa [mul_assoc] using tendsto_const_nhds.mul hlayer_tendsto
    have htracePart : Tendsto
        (fun k => (3 * isingFermionicGhostCoefficient) * traceRate k)
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul Htrace.trace_tendsto
    simpa using hmeshPart.add htracePart

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
