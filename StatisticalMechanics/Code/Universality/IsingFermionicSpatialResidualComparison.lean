/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual
import Code.Universality.IsingFermionicLocalizedPoissonLinearity











namespace StatMech.Universality

open Filter Set Topology
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm



noncomputable def vertexSpatialTargetResidual
    (n : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
    Option (FKIsingSquareFullVertexNode n) -> Real := by
  classical
  exact fun z =>
    if vertexDirichletBoundary n z then 0 else
      |isingFiniteWeightedLaplacian (vertexGhostConductance n) target z|


noncomputable def vertexSpatialTargetResidualPotential
    (n : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
    Option (FKIsingSquareFullVertexNode n) -> Real :=
  isingFiniteWeightedSpatialResidualPotential
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexSpatialTargetResidual n target)

theorem vertexSpatialTargetResidual_nonneg
    (n : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
    forall z, 0 <= vertexSpatialTargetResidual n target z := by
  intro z
  classical
  unfold vertexSpatialTargetResidual
  split_ifs <;> positivity

theorem vertexSpatialTargetResidualPotential_nonneg
    (n : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
    forall z, 0 <= vertexSpatialTargetResidualPotential n target z := by
  exact isingFiniteWeightedSpatialResidualPotential_nonneg
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexSpatialTargetResidual n target)
    (vertexSpatialTargetResidual_nonneg n target)

theorem vertexSpatialTargetResidualPotential_eq_sum_point
    (n : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
    vertexSpatialTargetResidualPotential n target =
      ∑ z ∈ (Finset.univ :
          Finset (Option (FKIsingSquareFullVertexNode n))),
        vertexSpatialTargetResidual n target z •
          vertexPointPoissonBarrier n z := by
  exact isingFiniteWeightedSpatialResidualPotential_eq_sum_point
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexSpatialTargetResidual n target)

theorem vertexSpatialTargetResidualPotential_le_sum_point_bound
    (n : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real)
    (x : Option (FKIsingSquareFullVertexNode n))
    (bound : Option (FKIsingSquareFullVertexNode n) -> Real)
    (hbound : forall z, vertexPointPoissonBarrier n z x <= bound z) :
    vertexSpatialTargetResidualPotential n target x <=
      ∑ z ∈ (Finset.univ :
          Finset (Option (FKIsingSquareFullVertexNode n))),
        vertexSpatialTargetResidual n target z * bound z := by
  exact isingFiniteWeightedSpatialResidualPotential_le_sum_point_bound
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexSpatialTargetResidual n target)
    bound x (vertexSpatialTargetResidual_nonneg n target) hbound


theorem vertexDirichlet_target_error_le_spatial_residual
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
    forall z, |vertexDirichlet n hn z - target z| <=
      vertexBoundaryConsistencyError n hn target +
        vertexSpatialTargetResidualPotential n target z := by
  apply isingFiniteWeighted_harmonic_approximation_of_spatial_residual
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexDirichlet n hn) target
    (vertexBoundaryConsistencyError n hn target)
    (vertexSpatialTargetResidual n target)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexDirichlet_harmonicOn n hn)
  · intro z hz
    rw [vertexDirichlet_boundary n hn z hz]
    exact isingFiniteWeightedBoundaryError_bound
      (vertexDirichletBoundary n) (vertexGhostPrimitive n hn) target z hz
  · exact vertexSpatialTargetResidual_nonneg n target
  · intro z hz
    simp [vertexSpatialTargetResidual, hz]



noncomputable def faceSpatialTargetResidual
    (n : Nat)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real) :
    Option (FKIsingSquareFullFaceNode n) -> Real := by
  classical
  exact fun z =>
    if faceDirichletBoundary n z then 0 else
      |isingFiniteWeightedLaplacian (faceGhostConductance n) target z|


noncomputable def faceSpatialTargetResidualPotential
    (n : Nat)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real) :
    Option (FKIsingSquareFullFaceNode n) -> Real :=
  isingFiniteWeightedSpatialResidualPotential
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) (faceSpatialTargetResidual n target)

theorem faceSpatialTargetResidual_nonneg
    (n : Nat)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real) :
    forall z, 0 <= faceSpatialTargetResidual n target z := by
  intro z
  classical
  unfold faceSpatialTargetResidual
  split_ifs <;> positivity

theorem faceSpatialTargetResidualPotential_nonneg
    (n : Nat)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real) :
    forall z, 0 <= faceSpatialTargetResidualPotential n target z := by
  exact isingFiniteWeightedSpatialResidualPotential_nonneg
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) (faceSpatialTargetResidual n target)
    (faceSpatialTargetResidual_nonneg n target)

theorem faceSpatialTargetResidualPotential_eq_sum_point
    (n : Nat)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real) :
    faceSpatialTargetResidualPotential n target =
      ∑ z ∈ (Finset.univ :
          Finset (Option (FKIsingSquareFullFaceNode n))),
        faceSpatialTargetResidual n target z •
          facePointPoissonBarrier n z := by
  exact isingFiniteWeightedSpatialResidualPotential_eq_sum_point
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) (faceSpatialTargetResidual n target)

theorem faceSpatialTargetResidualPotential_le_sum_point_bound
    (n : Nat)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real)
    (x : Option (FKIsingSquareFullFaceNode n))
    (bound : Option (FKIsingSquareFullFaceNode n) -> Real)
    (hbound : forall z, facePointPoissonBarrier n z x <= bound z) :
    faceSpatialTargetResidualPotential n target x <=
      ∑ z ∈ (Finset.univ :
          Finset (Option (FKIsingSquareFullFaceNode n))),
        faceSpatialTargetResidual n target z * bound z := by
  exact isingFiniteWeightedSpatialResidualPotential_le_sum_point_bound
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) (faceSpatialTargetResidual n target)
    bound x (faceSpatialTargetResidual_nonneg n target) hbound


theorem faceDirichlet_target_error_le_spatial_residual
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real) :
    forall z, |faceDirichlet n hn z - target z| <=
      faceBoundaryConsistencyError n hn target +
        faceSpatialTargetResidualPotential n target z := by
  apply isingFiniteWeighted_harmonic_approximation_of_spatial_residual
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceDirichlet n hn) target
    (faceBoundaryConsistencyError n hn target)
    (faceSpatialTargetResidual n target)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) (faceDirichlet_harmonicOn n hn)
  · intro z hz
    rw [faceDirichlet_boundary n hn z hz]
    exact isingFiniteWeightedBoundaryError_bound
      (faceDirichletBoundary n) (faceGhostPrimitive n hn) target z hz
  · exact faceSpatialTargetResidual_nonneg n target
  · intro z hz
    simp [faceSpatialTargetResidual, hz]



theorem physicalIncidence_target_error_le_spatial_residual
    (n : Nat) (hn : 0 < n)
    (vertexTarget : Option (FKIsingSquareFullVertexNode n) -> Real)
    (faceTarget : Option (FKIsingSquareFullFaceNode n) -> Real)
    (e : FKIsingSquareInteriorRadialIncidence n hn)
    (target : Real)
    (hvertexTarget : vertexTarget
      (some (fkIsingSquareInteriorRadialEndpoint n hn e)) = target)
    (hfaceTarget : faceTarget
      (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) = target) :
    let vertexError := vertexBoundaryConsistencyError n hn vertexTarget +
      vertexSpatialTargetResidualPotential n vertexTarget
        (some (fkIsingSquareInteriorRadialEndpoint n hn e))
    let faceError := faceBoundaryConsistencyError n hn faceTarget +
      faceSpatialTargetResidualPotential n faceTarget
        (some (fkIsingSquareFullFaceOfRadialIncidence n hn e))
    |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareInteriorRadialEndpoint n hn e) - target| <=
          max vertexError faceError /\
      |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (fkIsingSquareFullFaceOfRadialIncidence n hn e) - target| <=
          max vertexError faceError := by
  dsimp only
  apply physicalIncidence_close_of_dirichlet_close n hn e target
  · rw [<- hvertexTarget]
    exact (vertexDirichlet_target_error_le_spatial_residual
      n hn vertexTarget _).trans (le_max_left _ _)
  · rw [<- hfaceTarget]
    exact (faceDirichlet_target_error_le_spatial_residual
      n hn faceTarget _).trans (le_max_right _ _)




theorem physicalIncidence_uniform_convergence_of_spatial_residual
    (N : Nat -> Nat) (hN : forall k, 0 < N k)
    (vertexTarget : forall k,
      Option (FKIsingSquareFullVertexNode (N k)) -> Real)
    (faceTarget : forall k,
      Option (FKIsingSquareFullFaceNode (N k)) -> Real)
    (incidenceTarget : forall k,
      FKIsingSquareInteriorRadialIncidence (N k) (hN k) -> Real)
    (safe : forall k,
      FKIsingSquareInteriorRadialIncidence (N k) (hN k) -> Prop)
    (rate : Nat -> Real)
    (hvertexTarget : forall k e, vertexTarget k
      (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) =
        incidenceTarget k e)
    (hfaceTarget : forall k e, faceTarget k
      (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)) =
        incidenceTarget k e)
    (hvertexRate : forall k e, safe k e ->
      vertexBoundaryConsistencyError (N k) (hN k) (vertexTarget k) +
        vertexSpatialTargetResidualPotential (N k) (vertexTarget k)
          (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) <=
            rate k)
    (hfaceRate : forall k e, safe k e ->
      faceBoundaryConsistencyError (N k) (hN k) (faceTarget k) +
        faceSpatialTargetResidualPotential (N k) (faceTarget k)
          (some (fkIsingSquareFullFaceOfRadialIncidence
            (N k) (hN k) e)) <= rate k)
    (hrate : Tendsto rate atTop (nhds 0)) :
    forall eta : Real, 0 < eta -> Filter.Eventually (fun k =>
      forall e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        safe k e ->
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
                (N k) (hN k)).vertexPrimitive
              (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
                incidenceTarget k e| < eta /\
            |(fkIsingSquareBoundaryLayerCoordinateOneForm
                (N k) (hN k)).facePrimitive
              (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
                incidenceTarget k e| < eta) atTop := by
  intro eta heta
  have hevent : Filter.Eventually (fun k => rate k < eta) atTop :=
    hrate (Iio_mem_nhds heta)
  filter_upwards [hevent] with k hk
  intro e hsafe
  have h := physicalIncidence_target_error_le_spatial_residual
    (N k) (hN k) (vertexTarget k) (faceTarget k) e
    (incidenceTarget k e) (hvertexTarget k e) (hfaceTarget k e)
  have hmax : max
      (vertexBoundaryConsistencyError (N k) (hN k) (vertexTarget k) +
        vertexSpatialTargetResidualPotential (N k) (vertexTarget k)
          (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)))
      (faceBoundaryConsistencyError (N k) (hN k) (faceTarget k) +
        faceSpatialTargetResidualPotential (N k) (faceTarget k)
          (some (fkIsingSquareFullFaceOfRadialIncidence
            (N k) (hN k) e))) <= rate k :=
    max_le (hvertexRate k e hsafe) (hfaceRate k e hsafe)
  constructor
  · exact (h.1.trans hmax).trans_lt hk
  · exact (h.2.trans hmax).trans_lt hk

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
