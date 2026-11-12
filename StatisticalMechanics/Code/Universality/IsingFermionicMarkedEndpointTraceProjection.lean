/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicBoundaryProjectionSampling
import Code.Universality.IsingFermionicMarkedEndpointInputAssembly
import Code.Universality.IsingFermionicPolynomialEndpointConvergence









namespace StatMech.Universality

open Filter Metric Set
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm



noncomputable def isingFermionicQuadraticLipschitzConstant
    (C : NNReal) (k : Nat) : NNReal :=
  C * ⟨(((k + 1 : Nat) : Real) ^ 2), by positivity⟩



theorem tendsto_isingFermionicQuadraticLipschitz_mul_polynomialMesh
    (C : NNReal) :
    Tendsto (fun k =>
      (isingFermionicQuadraticLipschitzConstant C k : Real) *
        isingFermionicPolynomialMesh k) atTop (nhds 0) := by
  let u : Nat -> Real := fun k => 1 / ((k : Real) + 1)
  have hu : Tendsto u atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hCu : Tendsto (fun k => (C : Real) * u k) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hu
  convert hCu using 1
  funext k
  unfold isingFermionicQuadraticLipschitzConstant
    isingFermionicPolynomialMesh u
  have hk : (0 : Real) < (k : Real) + 1 := by positivity
  push_cast
  field_simp [hk.ne']
  rfl


structure LocalBoundaryTraceProjection
    (Phi : Complex -> Complex) (S : Set Complex) (L : NNReal)
    (sample : Complex) (value mesh : Real) where
  boundaryPoint : Complex
  sample_mem : sample ∈ S
  boundary_mem : boundaryPoint ∈ S
  trace : (Phi boundaryPoint).im = value
  dist_le_mesh : dist sample boundaryPoint <= mesh

theorem LocalBoundaryTraceProjection.error_le
    {Phi : Complex -> Complex} {S : Set Complex} {L : NNReal}
    {sample : Complex} {value mesh : Real}
    (P : LocalBoundaryTraceProjection Phi S L sample value mesh)
    (hPhi : LipschitzOnWith L (fun z => (Phi z).im) S) :
    |value - (Phi sample).im| <= L * mesh :=
  boundaryTrace_abs_sub_le_of_lipschitzOn Phi S L hPhi
    sample P.boundaryPoint value mesh P.sample_mem P.boundary_mem
    P.trace P.dist_le_mesh




structure PhysicalEndpointOrdinaryBoundaryProjectionData
    (N : Nat -> Nat) (Phi : Complex -> Complex)
    (mesh : Nat -> Real) (radius : Nat -> Nat) where
  lipschitzConstant : Nat -> NNReal
  region : Nat -> Set Complex
  imPhi_lipschitz : forall k,
    LipschitzOnWith (lipschitzConstant k)
      (fun z => (Phi z).im) (region k)
  vertexFixed : forall k x,
    fkIsingSquareFullVertexFixedBoundary (N k) x ->
    Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) ->
      LocalBoundaryTraceProjection Phi (region k) (lipschitzConstant k)
        (fullSquareScaledVertexEmbedding (N k) (mesh k) x) 0 (mesh k)
  faceFixed : forall k c,
    fkIsingSquareFullFaceFixedBoundary (N k) c ->
    Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) ->
      LocalBoundaryTraceProjection Phi (region k) (lipschitzConstant k)
        (fullSquareScaledFaceEmbedding (N k) (mesh k) c) 1 (mesh k)
  vertexFree : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      LocalBoundaryTraceProjection Phi (region k) (lipschitzConstant k)
        (fullSquareScaledVertexEmbedding (N k) (mesh k) x) 1 (mesh k)
  faceFree : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      LocalBoundaryTraceProjection Phi (region k) (lipschitzConstant k)
        (fullSquareScaledFaceEmbedding (N k) (mesh k) c) 0 (mesh k)



noncomputable def
    PhysicalEndpointOrdinaryBoundaryProjectionData.toOrdinaryTraceData
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (P : PhysicalEndpointOrdinaryBoundaryProjectionData N Phi mesh radius)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (htrace_tendsto : Tendsto
      (fun k => (P.lipschitzConstant k : Real) * mesh k)
      atTop (nhds 0)) :
    PhysicalEndpointOrdinaryTraceData N Phi mesh radius
      (fun k => (P.lipschitzConstant k : Real) * mesh k) where
  trace_nonneg k := mul_nonneg (P.lipschitzConstant k).2 (hmesh_nonneg k)
  vertexFixed k x hfixed hghost :=
    (P.vertexFixed k x hfixed hghost).error_le (P.imPhi_lipschitz k)
  faceFixed k c hfixed hghost :=
    (P.faceFixed k c hfixed hghost).error_le (P.imPhi_lipschitz k)
  vertexFree k x hfixed hghost hendpoint :=
    (P.vertexFree k x hfixed hghost hendpoint).error_le
      (P.imPhi_lipschitz k)
  faceFree k c hfixed hghost hendpoint :=
    (P.faceFree k c hfixed hghost hendpoint).error_le
      (P.imPhi_lipschitz k)
  trace_tendsto := htrace_tendsto




theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFourthOrderLayerProjectionAndRange
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    (Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius)
    (Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius)
    (P : PhysicalEndpointOrdinaryBoundaryProjectionData N Phi mesh radius)
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
    (htrace_tendsto : Tendsto
      (fun k => (P.lipschitzConstant k : Real) * mesh k)
      atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius
      (fun k => (P.lipschitzConstant k : Real) * mesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * mesh k +
        (3 * isingFermionicGhostCoefficient) *
          ((P.lipschitzConstant k : Real) * mesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) :=
  PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFourthOrderLayerTraceAndRange
      Hfourth Hlayer
      (P.toOrdinaryTraceData hmesh_nonneg htrace_tendsto)
      hvertexRadius hfaceRadius hmesh_nonneg hvertexRange hfaceRange
      hscaledFourth_tendsto hmesh_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
