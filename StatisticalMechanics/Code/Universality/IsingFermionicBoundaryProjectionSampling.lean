/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicEndpointClampedTarget











namespace StatMech.Universality

open Filter Metric Set
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm




theorem boundaryTrace_abs_sub_le_of_lipschitzOn
    (Phi : Complex -> Complex) (S : Set Complex) (L : NNReal)
    (hPhi : LipschitzOnWith L (fun z => (Phi z).im) S)
    (sample boundaryPoint : Complex) (value mesh : Real)
    (hsample : sample ∈ S) (hboundary : boundaryPoint ∈ S)
    (htrace : (Phi boundaryPoint).im = value)
    (hdist : dist sample boundaryPoint <= mesh) :
    |value - (Phi sample).im| <= L * mesh := by
  calc
    |value - (Phi sample).im| =
        dist (Phi sample).im (Phi boundaryPoint).im := by
      rw [Real.dist_eq, htrace, abs_sub_comm]
    _ <= L * dist sample boundaryPoint :=
      hPhi.dist_le_mul sample hsample boundaryPoint hboundary
    _ <= L * mesh := mul_le_mul_of_nonneg_left hdist L.2



structure PhysicalBoundaryProjectionSampling
    (N : Nat -> Nat) (mesh : Nat -> Real) (Phi : Complex -> Complex) where
  lipschitzConstant : NNReal
  imPhi_lipschitz : LipschitzWith lipschitzConstant (fun z => (Phi z).im)
  vertexProjection : forall k,
    {x : FKIsingSquareFullVertexNode (N k) //
      fkIsingSquareFullVertexFixedBoundary (N k) x} -> Complex
  faceProjection : forall k,
    {c : FKIsingSquareFullFaceNode (N k) //
      fkIsingSquareFullFaceFixedBoundary (N k) c} -> Complex
  vertexProjection_trace : forall k x, (Phi (vertexProjection k x)).im = 0
  faceProjection_trace : forall k c, (Phi (faceProjection k c)).im = 1
  vertexProjection_dist_le_mesh : forall k x,
    dist (fullSquareScaledVertexEmbedding (N k) (mesh k) x.1)
      (vertexProjection k x) <= mesh k
  faceProjection_dist_le_mesh : forall k c,
    dist (fullSquareScaledFaceEmbedding (N k) (mesh k) c.1)
      (faceProjection k c) <= mesh k



theorem PhysicalBoundaryProjectionSampling.vertexTrace_abs_le
    {N : Nat -> Nat} {mesh : Nat -> Real} {Phi : Complex -> Complex}
    (B : PhysicalBoundaryProjectionSampling N mesh Phi)
    (k : Nat) (x : FKIsingSquareFullVertexNode (N k))
    (hx : fkIsingSquareFullVertexFixedBoundary (N k) x) :
    |0 - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| <=
      B.lipschitzConstant * mesh k := by
  let y : {z : FKIsingSquareFullVertexNode (N k) //
      fkIsingSquareFullVertexFixedBoundary (N k) z} := ⟨x, hx⟩
  exact boundaryTrace_abs_sub_le_of_lipschitz
    Phi B.lipschitzConstant B.imPhi_lipschitz
    (fullSquareScaledVertexEmbedding (N k) (mesh k) x)
    (B.vertexProjection k y) 0 (mesh k)
    (B.vertexProjection_trace k y)
    (B.vertexProjection_dist_le_mesh k y)



theorem PhysicalBoundaryProjectionSampling.faceTrace_abs_le
    {N : Nat -> Nat} {mesh : Nat -> Real} {Phi : Complex -> Complex}
    (B : PhysicalBoundaryProjectionSampling N mesh Phi)
    (k : Nat) (c : FKIsingSquareFullFaceNode (N k))
    (hc : fkIsingSquareFullFaceFixedBoundary (N k) c) :
    |1 - (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im| <=
      B.lipschitzConstant * mesh k := by
  let d : {z : FKIsingSquareFullFaceNode (N k) //
      fkIsingSquareFullFaceFixedBoundary (N k) z} := ⟨c, hc⟩
  exact boundaryTrace_abs_sub_le_of_lipschitz
    Phi B.lipschitzConstant B.imPhi_lipschitz
    (fullSquareScaledFaceEmbedding (N k) (mesh k) c)
    (B.faceProjection k d) 1 (mesh k)
    (B.faceProjection_trace k d)
    (B.faceProjection_dist_le_mesh k d)


theorem PhysicalBoundaryProjectionSampling.traceRate_tendsto_zero
    {N : Nat -> Nat} {mesh : Nat -> Real} {Phi : Complex -> Complex}
    (B : PhysicalBoundaryProjectionSampling N mesh Phi)
    (hmesh : Tendsto mesh atTop (nhds 0)) :
    Tendsto (fun k => (B.lipschitzConstant : Real) * mesh k)
      atTop (nhds 0) := by
  simpa using tendsto_const_nhds.mul hmesh



theorem PhysicalBoundaryProjectionSampling.vertexClamped_laplacian_le
    {N : Nat -> Nat} {mesh : Nat -> Real} {Phi : Complex -> Complex}
    (B : PhysicalBoundaryProjectionSampling N mesh Phi)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (k : Nat) (sampleBound : Real)
    (x : FKIsingSquareFullVertexNode (N k))
    (hx : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
    (hsample :
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
        (fun y => (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) x| <= sampleBound) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
      (fun y => vertexBoundaryClampedSampledTarget
        (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi
          (some y)) x| <=
        sampleBound + 4 * (B.lipschitzConstant * mesh k) := by
  apply vertexBoundaryClampedSampledTarget_laplacian_le
    (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi
    sampleBound (B.lipschitzConstant * mesh k)
  · exact mul_nonneg B.lipschitzConstant.2 (hmesh_nonneg k)
  · exact fun y hy => B.vertexTrace_abs_le k y hy
  · exact hx
  · exact hsample



theorem PhysicalBoundaryProjectionSampling.faceClamped_laplacian_le
    {N : Nat -> Nat} {mesh : Nat -> Real} {Phi : Complex -> Complex}
    (B : PhysicalBoundaryProjectionSampling N mesh Phi)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (k : Nat) (sampleBound : Real)
    (c : FKIsingSquareFullFaceNode (N k))
    (hc : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
    (hsample :
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
        (fun d => (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) c| <= sampleBound) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
      (fun d => faceBoundaryClampedSampledTarget
        (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi
          (some d)) c| <=
        sampleBound + 4 * (B.lipschitzConstant * mesh k) := by
  apply faceBoundaryClampedSampledTarget_laplacian_le
    (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi
    sampleBound (B.lipschitzConstant * mesh k)
  · exact mul_nonneg B.lipschitzConstant.2 (hmesh_nonneg k)
  · exact fun d hd => B.faceTrace_abs_le k d hd
  · exact hc
  · exact hsample



theorem PhysicalBoundaryProjectionSampling.vertexClamped_weightedLaplacian_le
    {N : Nat -> Nat} {mesh : Nat -> Real} {Phi : Complex -> Complex}
    (B : PhysicalBoundaryProjectionSampling N mesh Phi)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (k : Nat) (sampleBound : Real)
    (x : FKIsingSquareFullVertexNode (N k))
    (hx : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
    (hsample :
      |isingFiniteWeightedLaplacian (vertexGhostConductance (N k))
        (vertexSampledImaginaryTarget (N k)
          (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi)
        (some x)| <= sampleBound) :
    |isingFiniteWeightedLaplacian (vertexGhostConductance (N k))
      (vertexBoundaryClampedSampledTarget (N k)
        (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi) (some x)| <=
        sampleBound + 4 * (B.lipschitzConstant * mesh k) := by
  let clamped := isingFiniteWeightedLaplacian
    (vertexGhostConductance (N k))
    (vertexBoundaryClampedSampledTarget (N k)
      (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi) (some x)
  let sampled := isingFiniteWeightedLaplacian
    (vertexGhostConductance (N k))
    (vertexSampledImaginaryTarget (N k)
      (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi) (some x)
  have hdiff : |clamped - sampled| <=
      4 * (B.lipschitzConstant * mesh k) :=
    vertexBoundaryClampedSampledTarget_weightedLaplacian_sub_le_four
      (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi
      (B.lipschitzConstant * mesh k)
      (mul_nonneg B.lipschitzConstant.2 (hmesh_nonneg k))
      (fun y hy => B.vertexTrace_abs_le k y hy) x hx
  calc
    |clamped| = |(clamped - sampled) + sampled| := by ring_nf
    _ <= |clamped - sampled| + |sampled| := abs_add_le _ _
    _ <= 4 * (B.lipschitzConstant * mesh k) + sampleBound :=
      add_le_add hdiff hsample
    _ = sampleBound + 4 * (B.lipschitzConstant * mesh k) := by ring



theorem PhysicalBoundaryProjectionSampling.faceClamped_weightedLaplacian_le
    {N : Nat -> Nat} {mesh : Nat -> Real} {Phi : Complex -> Complex}
    (B : PhysicalBoundaryProjectionSampling N mesh Phi)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (k : Nat) (sampleBound : Real)
    (c : FKIsingSquareFullFaceNode (N k))
    (hc : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
    (hsample :
      |isingFiniteWeightedLaplacian (faceGhostConductance (N k))
        (faceSampledImaginaryTarget (N k)
          (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi)
        (some c)| <= sampleBound) :
    |isingFiniteWeightedLaplacian (faceGhostConductance (N k))
      (faceBoundaryClampedSampledTarget (N k)
        (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi) (some c)| <=
        sampleBound + 4 * (B.lipschitzConstant * mesh k) := by
  let clamped := isingFiniteWeightedLaplacian
    (faceGhostConductance (N k))
    (faceBoundaryClampedSampledTarget (N k)
      (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi) (some c)
  let sampled := isingFiniteWeightedLaplacian
    (faceGhostConductance (N k))
    (faceSampledImaginaryTarget (N k)
      (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi) (some c)
  have hdiff : |clamped - sampled| <=
      4 * (B.lipschitzConstant * mesh k) :=
    faceBoundaryClampedSampledTarget_weightedLaplacian_sub_le_four
      (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi
      (B.lipschitzConstant * mesh k)
      (mul_nonneg B.lipschitzConstant.2 (hmesh_nonneg k))
      (fun d hd => B.faceTrace_abs_le k d hd) c hc
  calc
    |clamped| = |(clamped - sampled) + sampled| := by ring_nf
    _ <= |clamped - sampled| + |sampled| := abs_add_le _ _
    _ <= 4 * (B.lipschitzConstant * mesh k) + sampleBound :=
      add_le_add hdiff hsample
    _ = sampleBound + 4 * (B.lipschitzConstant * mesh k) := by ring

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
