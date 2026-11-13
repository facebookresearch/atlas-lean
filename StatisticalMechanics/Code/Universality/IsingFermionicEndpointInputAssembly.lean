/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicEndpointRangeBound
import Mathlib.Analysis.Calculus.MeanValue









namespace StatMech.Universality

open Filter Set Topology

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm



structure PhysicalEndpointFourthOrderBulkData
    (N : Nat -> Nat) (Phi : Complex -> Complex)
    (mesh : Nat -> Real) (radius : Nat -> Nat) where
  boundOne : Real
  boundTwo : Real
  boundSum_nonneg : 0 <= boundOne + boundTwo
  vertex : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      DirectionalFourthOrderHarmonicData (fun z => (Phi z).im)
        (fullSquareScaledVertexEmbedding (N k) (mesh k) x)
        boundOne boundTwo
  face : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      DirectionalFourthOrderHarmonicData (fun z => (Phi z).im)
        (fullSquareScaledFaceEmbedding (N k) (mesh k) c)
        boundOne boundTwo

theorem PhysicalEndpointFourthOrderBulkData.vertexLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointFourthOrderBulkData N Phi mesh radius)
    (k : Nat) (x : FKIsingSquareFullVertexNode (N k))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0)
    (hendpoint : Not (vertexMarkedEndpointLayer
      (N k) (radius k) (some x))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
      (fun y => (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) y)).im) x| <=
        (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareVertex_bulk_directions (N k) x hfixed hghost
  obtain ⟨hgOne, hgTwo, hfourthOne, hfourthTwo, hharmonic⟩ :=
    H.vertex k x hfixed hghost hendpoint
  exact fullSquareScaledVertex_sampledLaplacian_le_fourthOrder
    (N k) (mesh k) (fun z => (Phi z).im) x
    heast hnorth hwest hsouth H.boundOne H.boundTwo
    hgOne hgTwo hfourthOne hfourthTwo hharmonic

theorem PhysicalEndpointFourthOrderBulkData.faceLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointFourthOrderBulkData N Phi mesh radius)
    (k : Nat) (c : FKIsingSquareFullFaceNode (N k))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0)
    (hendpoint : Not (faceMarkedEndpointLayer
      (N k) (radius k) (some c))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
      (fun d => (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) d)).im) c| <=
        (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareFace_bulk_coordinates (N k) c hfixed hghost
  obtain ⟨hgOne, hgTwo, hfourthOne, hfourthTwo, hharmonic⟩ :=
    H.face k c hfixed hghost hendpoint
  exact fullSquareScaledFace_sampledLaplacian_le_fourthOrder
    (N k) (mesh k) (fun z => (Phi z).im) c
    heast hnorth hwest hsouth H.boundOne H.boundTwo
    hgOne hgTwo hfourthOne hfourthTwo hharmonic



theorem PhysicalEndpointLocalizedRobinInputs.ofLocalizedFourthOrderAndRange
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real}
    {radius : Nat -> Nat} (layerRate : Nat -> Real)
    (Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (hlayer_nonneg : forall k, 0 <= layerRate k)
    (hvertexFixed : forall k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x ->
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0)
    (hfaceFixed : forall k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c ->
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1)
    (hvertexFree : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1)
    (hfaceFree : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0)
    (hvertexLayer : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
          (fun y => (Phi (fullSquareScaledVertexEmbedding
            (N k) (mesh k) y)).im) x| <= layerRate k)
    (hfaceLayer : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
          (fun d => (Phi (fullSquareScaledFaceEmbedding
            (N k) (mesh k) d)).im) c| <= layerRate k)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
    (hscaledFourth_tendsto : Tendsto
      (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2)
      atTop (nhds 0))
    (hlayer_tendsto : Tendsto layerRate atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedRobinInputs N hN Phi mesh radius
      (fun k =>
        (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      layerRate (fun _ => 4) := by
  refine
    { mesh_nonneg := hmesh_nonneg
      bulk_nonneg := ?_
      layer_nonneg := hlayer_nonneg
      endpoint_nonneg := fun _ => by norm_num
      vertexFixed := hvertexFixed
      faceFixed := hfaceFixed
      vertexFree := hvertexFree
      faceFree := hfaceFree
      vertexBulk := ?_
      faceBulk := ?_
      vertexLayer := hvertexLayer
      faceLayer := hfaceLayer
      vertexEndpoint := ?_
      faceEndpoint := ?_
      scaledBulk_tendsto := ?_
      layer_tendsto := hlayer_tendsto
      mesh_tendsto := hmesh_tendsto }
  · intro k
    exact div_nonneg
      (mul_nonneg Hfourth.boundSum_nonneg (pow_nonneg (abs_nonneg _) 4))
      (by norm_num)
  · exact fun k x hfixed hghost hendpoint =>
      Hfourth.vertexLaplacian k x hfixed hghost hendpoint
  · exact fun k c hfixed hghost hendpoint =>
      Hfourth.faceLaplacian k c hfixed hghost hendpoint
  · intro k x _hfixed _hendpoint
    exact fullSquareVertex_sampledLaplacian_le_four_of_unitRange
      (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k))
      Phi (hvertexRange k) x
  · intro k c _hfixed _hendpoint
    exact fullSquareFace_sampledLaplacian_le_four_of_unitRange
      (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k))
      Phi (hfaceRange k) c
  · have hconstant : Tendsto
        (fun _ : Nat => (Hfourth.boundOne + Hfourth.boundTwo) / 12)
        atTop (nhds ((Hfourth.boundOne + Hfourth.boundTwo) / 12)) :=
      tendsto_const_nhds
    have hproduct := hconstant.mul hscaledFourth_tendsto
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hproduct



structure PhysicalEndpointLayerIncrementData
    (N : Nat -> Nat) (Phi : Complex -> Complex)
    (mesh : Nat -> Real) (radius : Nat -> Nat) where
  constant : NNReal
  vertex : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
    forall y, (fkIsingSquareFullVertexGraph (N k)).Adj x y ->
      |(Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im -
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| <=
          constant * mesh k
  face : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
    forall d, (fkIsingSquareFullFaceGraph (N k)).Adj c d ->
      |(Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im -
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im| <=
          constant * mesh k



noncomputable def PhysicalEndpointLayerIncrementData.ofLipschitzOn
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (S : Set Complex) (L : NNReal)
    (hPhi : LipschitzOnWith L (fun z => (Phi z).im) S)
    (hmesh : forall k, 0 <= mesh k)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ S /\
          forall y, (fkIsingSquareFullVertexGraph (N k)).Adj x y ->
            fullSquareScaledVertexEmbedding (N k) (mesh k) y ∈ S)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ S /\
          forall d, (fkIsingSquareFullFaceGraph (N k)).Adj c d ->
            fullSquareScaledFaceEmbedding (N k) (mesh k) d ∈ S) :
    PhysicalEndpointLayerIncrementData N Phi mesh radius where
  constant := 2 * L
  vertex k x hfixed hghost hendpoint y hxy := by
    obtain ⟨hx, hy⟩ := hvertex k x hfixed hghost hendpoint
    rw [← Real.dist_eq]
    calc
      dist
          (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im
          (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <=
          L * dist
            (fullSquareScaledVertexEmbedding (N k) (mesh k) y)
            (fullSquareScaledVertexEmbedding (N k) (mesh k) x) :=
        hPhi.dist_le_mul _ (hy y hxy) _ hx
      _ <= L * (2 * |mesh k|) := by
        gcongr
        exact fullSquareScaledVertexEmbedding_dist_le_two_abs
          (N k) (mesh k) x y hxy
      _ = (2 * L : NNReal) * mesh k := by
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
          L * dist
            (fullSquareScaledFaceEmbedding (N k) (mesh k) d)
            (fullSquareScaledFaceEmbedding (N k) (mesh k) c) :=
        hPhi.dist_le_mul _ (hd d hcd) _ hc
      _ <= L * (2 * |mesh k|) := by
        gcongr
        exact fullSquareScaledFaceEmbedding_dist_le_two_abs
          (N k) (mesh k) c d hcd
      _ = (2 * L : NNReal) * mesh k := by
        rw [abs_of_nonneg (hmesh k)]
        norm_num
        ring



noncomputable def PhysicalEndpointLayerIncrementData.ofFDerivBoundOnConvex
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (S : Set Complex) (L : NNReal)
    (hPhi : forall z, z ∈ S ->
      DifferentiableAt Real (fun w => (Phi w).im) z)
    (hderiv : forall z, z ∈ S ->
      ‖fderiv Real (fun w => (Phi w).im) z‖₊ <= L)
    (hconvex : Convex Real S)
    (hmesh : forall k, 0 <= mesh k)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ S /\
          forall y, (fkIsingSquareFullVertexGraph (N k)).Adj x y ->
            fullSquareScaledVertexEmbedding (N k) (mesh k) y ∈ S)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ S /\
          forall d, (fkIsingSquareFullFaceGraph (N k)).Adj c d ->
            fullSquareScaledFaceEmbedding (N k) (mesh k) d ∈ S) :
    PhysicalEndpointLayerIncrementData N Phi mesh radius :=
  PhysicalEndpointLayerIncrementData.ofLipschitzOn S L
    (hconvex.lipschitzOnWith_of_nnnorm_fderiv_le hPhi hderiv)
    hmesh hvertex hface

theorem PhysicalEndpointLayerIncrementData.vertexLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointLayerIncrementData N Phi mesh radius)
    (hmesh : forall k, 0 <= mesh k) (k : Nat)
    (x : FKIsingSquareFullVertexNode (N k))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
    (hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x)
    (hendpoint : Not (vertexMarkedEndpointLayer
      (N k) (radius k) (some x))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
      (fun y => (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) y)).im) x| <= 4 * H.constant * mesh k := by
  have hbound := isingFiniteGraphLaplacian_abs_le_four_mul
    (fkIsingSquareFullVertexGraph (N k))
    (fun y => (Phi (fullSquareScaledVertexEmbedding
      (N k) (mesh k) y)).im) x (H.constant * mesh k)
    (mul_nonneg H.constant.2 (hmesh k))
    (fullVertex_neighbor_card_le_four (N k) x)
    (H.vertex k x hfixed hghost hendpoint)
  simpa [mul_assoc] using hbound

theorem PhysicalEndpointLayerIncrementData.faceLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointLayerIncrementData N Phi mesh radius)
    (hmesh : forall k, 0 <= mesh k) (k : Nat)
    (c : FKIsingSquareFullFaceNode (N k))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
    (hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c)
    (hendpoint : Not (faceMarkedEndpointLayer
      (N k) (radius k) (some c))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
      (fun d => (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) d)).im) c| <= 4 * H.constant * mesh k := by
  have hbound := isingFiniteGraphLaplacian_abs_le_four_mul
    (fkIsingSquareFullFaceGraph (N k))
    (fun d => (Phi (fullSquareScaledFaceEmbedding
      (N k) (mesh k) d)).im) c (H.constant * mesh k)
    (mul_nonneg H.constant.2 (hmesh k))
    (fullFace_neighbor_card_le_four (N k) c)
    (H.face k c hfixed hghost hendpoint)
  simpa [mul_assoc] using hbound



theorem PhysicalEndpointLocalizedRobinInputs.ofLocalizedFourthOrderLayerAndRange
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real}
    {radius : Nat -> Nat}
    (Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius)
    (Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (hvertexFixed : forall k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x ->
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0)
    (hfaceFixed : forall k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c ->
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1)
    (hvertexFree : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1)
    (hfaceFree : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
    (hscaledFourth_tendsto : Tendsto
      (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2)
      atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedRobinInputs N hN Phi mesh radius
      (fun k =>
        (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      (fun k => 4 * Hlayer.constant * mesh k) (fun _ => 4) := by
  apply PhysicalEndpointLocalizedRobinInputs.ofLocalizedFourthOrderAndRange
    (fun k => 4 * Hlayer.constant * mesh k) Hfourth hmesh_nonneg
  · intro k
    exact mul_nonneg (mul_nonneg (by norm_num) Hlayer.constant.2)
      (hmesh_nonneg k)
  · exact hvertexFixed
  · exact hfaceFixed
  · exact hvertexFree
  · exact hfaceFree
  · exact Hlayer.vertexLaplacian hmesh_nonneg
  · exact Hlayer.faceLaplacian hmesh_nonneg
  · exact hvertexRange
  · exact hfaceRange
  · exact hscaledFourth_tendsto
  · simpa using tendsto_const_nhds.mul hmesh_tendsto
  · exact hmesh_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
