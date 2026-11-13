/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate








namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm



noncomputable def vertexCalibratedRobinEmbedding
    (n : Nat) (hn : 0 < n) (scale : Real)
    (x : FKIsingSquareFullVertexNode n) : Complex :=
  ⟨(fullSquareScaledVertexEmbedding n scale x).re,
    vertexDirichlet n hn (some x)⟩



noncomputable def faceCalibratedRobinEmbedding
    (n : Nat) (hn : 0 < n) (scale : Real)
    (c : FKIsingSquareFullFaceNode n) : Complex :=
  ⟨(fullSquareScaledFaceEmbedding n scale c).re,
    faceDirichlet n hn (some c)⟩

@[simp] theorem vertexCalibratedRobinEmbedding_im
    (n : Nat) (hn : 0 < n) (scale : Real)
    (x : FKIsingSquareFullVertexNode n) :
    (vertexCalibratedRobinEmbedding n hn scale x).im =
      vertexDirichlet n hn (some x) := rfl

@[simp] theorem faceCalibratedRobinEmbedding_im
    (n : Nat) (hn : 0 < n) (scale : Real)
    (c : FKIsingSquareFullFaceNode n) :
    (faceCalibratedRobinEmbedding n hn scale c).im =
      faceDirichlet n hn (some c) := rfl



theorem vertexSampledImaginaryTarget_calibrated
    (n : Nat) (hn : 0 < n) (scale : Real) :
    vertexSampledImaginaryTarget n
        (vertexCalibratedRobinEmbedding n hn scale) id =
      vertexDirichlet n hn := by
  funext x
  cases x with
  | none =>
      rw [vertexDirichlet_boundary n hn none]
      · rfl
      · simp [vertexDirichletBoundary, isingFiniteGhostBoundaryWith]
  | some x => rfl



theorem faceSampledImaginaryTarget_calibrated
    (n : Nat) (hn : 0 < n) (scale : Real) :
    faceSampledImaginaryTarget n
        (faceCalibratedRobinEmbedding n hn scale) id =
      faceDirichlet n hn := by
  funext c
  cases c with
  | none =>
      rw [faceDirichlet_boundary n hn none]
      · rfl
      · simp [faceDirichletBoundary, isingFiniteGhostBoundaryWith]
  | some c => rfl


theorem vertexCalibratedRobin_boundaryConsistencyError_eq_zero
    (n : Nat) (hn : 0 < n) (scale : Real) :
    vertexBoundaryConsistencyError n hn
      (vertexSampledImaginaryTarget n
        (vertexCalibratedRobinEmbedding n hn scale) id) = 0 := by
  rw [vertexSampledImaginaryTarget_calibrated]
  apply le_antisymm
  · apply isingFiniteWeightedBoundaryError_le
      (vertexDirichletBoundary n) (vertexGhostPrimitive n hn)
      (vertexDirichlet n hn) 0 (le_refl 0)
    intro x hx
    rw [vertexDirichlet_boundary n hn x hx]
    simp
  · exact isingFiniteWeightedBoundaryError_nonneg
      (vertexDirichletBoundary n) (vertexGhostPrimitive n hn)
      (vertexDirichlet n hn)


theorem faceCalibratedRobin_boundaryConsistencyError_eq_zero
    (n : Nat) (hn : 0 < n) (scale : Real) :
    faceBoundaryConsistencyError n hn
      (faceSampledImaginaryTarget n
        (faceCalibratedRobinEmbedding n hn scale) id) = 0 := by
  rw [faceSampledImaginaryTarget_calibrated]
  apply le_antisymm
  · apply isingFiniteWeightedBoundaryError_le
      (faceDirichletBoundary n) (faceGhostPrimitive n hn)
      (faceDirichlet n hn) 0 (le_refl 0)
    intro c hc
    rw [faceDirichlet_boundary n hn c hc]
    simp
  · exact isingFiniteWeightedBoundaryError_nonneg
      (faceDirichletBoundary n) (faceGhostPrimitive n hn)
      (faceDirichlet n hn)



theorem vertexCalibratedRobin_targetResidual_eq_zero
    (n : Nat) (hn : 0 < n) (scale : Real) :
    vertexTargetResidual n
      (vertexSampledImaginaryTarget n
        (vertexCalibratedRobinEmbedding n hn scale) id) = 0 := by
  rw [vertexSampledImaginaryTarget_calibrated]
  apply le_antisymm
  · apply isingFiniteWeightedTargetResidual_le
      (vertexGhostConductance n) (vertexDirichletBoundary n)
      (vertexDirichlet n hn) 0 (le_refl 0)
    intro x hx
    rw [vertexDirichlet_harmonicOn n hn x hx]
    simp
  · exact isingFiniteWeightedTargetResidual_nonneg
      (vertexGhostConductance n) (vertexDirichletBoundary n)
      (vertexDirichlet n hn)



theorem faceCalibratedRobin_targetResidual_eq_zero
    (n : Nat) (hn : 0 < n) (scale : Real) :
    faceTargetResidual n
      (faceSampledImaginaryTarget n
        (faceCalibratedRobinEmbedding n hn scale) id) = 0 := by
  rw [faceSampledImaginaryTarget_calibrated]
  apply le_antisymm
  · apply isingFiniteWeightedTargetResidual_le
      (faceGhostConductance n) (faceDirichletBoundary n)
      (faceDirichlet n hn) 0 (le_refl 0)
    intro c hc
    rw [faceDirichlet_harmonicOn n hn c hc]
    simp
  · exact isingFiniteWeightedTargetResidual_nonneg
      (faceGhostConductance n) (faceDirichletBoundary n)
      (faceDirichlet n hn)


theorem vertexCalibratedRobin_targetConsistencyError_eq_zero
    (n : Nat) (hn : 0 < n) (scale : Real) :
    vertexTargetConsistencyError n hn
      (vertexSampledImaginaryTarget n
        (vertexCalibratedRobinEmbedding n hn scale) id) = 0 := by
  unfold vertexTargetConsistencyError
  rw [vertexCalibratedRobin_boundaryConsistencyError_eq_zero,
    vertexCalibratedRobin_targetResidual_eq_zero]
  ring


theorem faceCalibratedRobin_targetConsistencyError_eq_zero
    (n : Nat) (hn : 0 < n) (scale : Real) :
    faceTargetConsistencyError n hn
      (faceSampledImaginaryTarget n
        (faceCalibratedRobinEmbedding n hn scale) id) = 0 := by
  unfold faceTargetConsistencyError
  rw [faceCalibratedRobin_boundaryConsistencyError_eq_zero,
    faceCalibratedRobin_targetResidual_eq_zero]
  ring

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
