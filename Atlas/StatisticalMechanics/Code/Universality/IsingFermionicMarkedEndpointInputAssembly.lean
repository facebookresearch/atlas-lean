/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicMarkedEndpointClampedTarget








namespace StatMech.Universality

open Filter
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm


structure PhysicalEndpointOrdinaryTraceData
    (N : Nat -> Nat) (Phi : Complex -> Complex)
    (mesh : Nat -> Real) (radius : Nat -> Nat)
    (traceRate : Nat -> Real) where
  trace_nonneg : forall k, 0 <= traceRate k
  vertexFixed : forall k x,
    fkIsingSquareFullVertexFixedBoundary (N k) x ->
    Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) ->
      |0 - (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) x)).im| <= traceRate k
  faceFixed : forall k c,
    fkIsingSquareFullFaceFixedBoundary (N k) c ->
    Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) ->
      |1 - (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) c)).im| <= traceRate k
  vertexFree : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      |1 - (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) x)).im| <= traceRate k
  faceFree : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      |0 - (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) c)).im| <= traceRate k
  trace_tendsto : Tendsto traceRate atTop (nhds 0)




theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFourthOrderLayerTraceAndRange
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    {traceRate : Nat -> Real}
    (Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius)
    (Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius)
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
    (hscaledFourth_tendsto : Tendsto
      (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius
      traceRate
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * mesh k +
        (3 * isingFermionicGhostCoefficient) * traceRate k)
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  apply PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofSampledResiduals
    hvertexRadius hfaceRadius
  · exact Htrace.trace_nonneg
  · intro k
    exact div_nonneg
      (mul_nonneg Hfourth.boundSum_nonneg (pow_nonneg (abs_nonneg _) 4))
      (by norm_num)
  · intro k
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) Hlayer.constant.2)
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
      _ <= 4 * Hlayer.constant * mesh k +
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
      _ <= 4 * Hlayer.constant * mesh k +
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
  · have hconstant : Tendsto
        (fun _ : Nat => (Hfourth.boundOne + Hfourth.boundTwo) / 12)
        atTop (nhds ((Hfourth.boundOne + Hfourth.boundTwo) / 12)) :=
      tendsto_const_nhds
    have hproduct := hconstant.mul hscaledFourth_tendsto
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hproduct
  · have hmeshPart : Tendsto
        (fun k => (4 * (Hlayer.constant : Real)) * mesh k)
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hmesh_tendsto
    have htracePart : Tendsto
        (fun k => (3 * isingFermionicGhostCoefficient) * traceRate k)
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul Htrace.trace_tendsto
    simpa using hmeshPart.add htracePart

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
