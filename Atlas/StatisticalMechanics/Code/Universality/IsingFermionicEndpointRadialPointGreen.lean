/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicEndpointRadialShellCardinality









namespace StatMech.Universality

open Finset SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm


noncomputable def endpointRadialGreenConstant : Real :=
  2 * (1 + 1 / isingFermionicGhostCoefficient)

theorem endpointRadialGreenConstant_nonneg :
    0 <= endpointRadialGreenConstant := by
  unfold endpointRadialGreenConstant
  have h : 0 <= 1 / isingFermionicGhostCoefficient :=
    one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le
  nlinarith

private theorem endpointRadial_product_div_half_le
    (n r : Nat) (hn : 0 < n) :
    (r : Real) * ((r : Real) + 1 / isingFermionicGhostCoefficient) /
        ((n : Real) / 2) <=
      endpointRadialGreenConstant * ((r + 1 : Nat) : Real) ^ 2 /
        (n : Real) := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hr : (0 : Real) <= r := by positivity
  have hc : (0 : Real) <= 1 / isingFermionicGhostCoefficient :=
    one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le
  have hproduct : (r : Real) *
      ((r : Real) + 1 / isingFermionicGhostCoefficient) <=
        (1 + 1 / isingFermionicGhostCoefficient) *
          ((r + 1 : Nat) : Real) ^ 2 := by
    push_cast
    nlinarith [mul_nonneg hr hc]
  calc
    (r : Real) * ((r : Real) + 1 / isingFermionicGhostCoefficient) /
          ((n : Real) / 2) =
        2 * ((r : Real) *
          ((r : Real) + 1 / isingFermionicGhostCoefficient)) /
            (n : Real) := by
      field_simp [hnR.ne']
    _ <= 2 * ((1 + 1 / isingFermionicGhostCoefficient) *
          ((r + 1 : Nat) : Real) ^ 2) / (n : Real) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hproduct (by norm_num)) hnR.le
    _ = endpointRadialGreenConstant * ((r + 1 : Nat) : Real) ^ 2 /
          (n : Real) := by
      unfold endpointRadialGreenConstant
      ring


theorem vertexPointPoissonBarrier_le_endpointRadial_of_halfColumn
    (n : Nat) (hn : 0 < n)
    (observation : FKIsingSquareFullVertexNode n)
    (z : Option (FKIsingSquareFullVertexNode n))
    (hz : Not (vertexDirichletBoundary n z))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n observation))
    (hright : observation.1 0 < (n : Int))
    (hbottom : -(n : Int) < observation.1 1)
    (htop : observation.1 1 < (n : Int))
    (hhalf : ((n : Real) / 2) <=
      fullVertexColumnIndex n observation) :
    vertexPointPoissonBarrier n z (some observation) <=
      (vertexEndpointRadialShell n z : Real) *
        ((vertexEndpointRadialShell n z : Real) +
          1 / isingFermionicGhostCoefficient) / ((n : Real) / 2) := by
  cases z with
  | none =>
      exact False.elim (hz (by
        simp [vertexDirichletBoundary, isingFiniteGhostBoundaryWith]))
  | some y =>
      have hobservation : Not (vertexDirichletBoundary n (some observation)) := by
        simpa [vertexDirichletBoundary, isingFiniteGhostBoundaryWith] using hfixed
      unfold vertexPointPoissonBarrier
      rw [isingFiniteWeightedPointPoissonBarrier_comm
        (vertexGhostGraph n) (vertexGhostConductance n)
        (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
        (vertexGhostConductance_pos_of_adj n)
        (vertexGhost_reaches_boundary n)
        (isingFiniteGhostConductance_comm
          (fkIsingSquareFullVertexGraph n)
          (isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n)))
        (some y) (some observation) hz hobservation]
      have hdistance : (0 : Real) < (n : Real) / 2 := by positivity
      have hrecip : 0 <= 1 / isingFermionicGhostCoefficient :=
        one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le
      by_cases hlower : fullVertexRowIndex n y <=
          2 * n - fullVertexRowIndex n y
      · apply vertexPointPoissonBarrier_le_lowerLeftRadius
          n (vertexEndpointRadialShell n (some y)) ((n : Real) / 2)
          observation y hn hfixed hright hbottom htop
        · simp [vertexEndpointRadialShell, min_eq_left hlower]
        · exact hdistance
        · have hrow : 0 <=
              (fullVertexRowIndex n observation : Real) := by
            positivity
          linarith
      · have hupper : 2 * n - fullVertexRowIndex n y <=
            fullVertexRowIndex n y := by omega
        apply vertexPointPoissonBarrier_le_upperLeftRadius
          n (vertexEndpointRadialShell n (some y)) ((n : Real) / 2)
          observation y hn hfixed hright hbottom htop
        · simp [vertexEndpointRadialShell, min_eq_right hupper]
        · exact hdistance
        · have hrow : 0 <=
              ((2 * n - fullVertexRowIndex n observation : Nat) : Real) := by
            positivity
          linarith


theorem facePointPoissonBarrier_le_endpointRadial_of_halfColumn
    (n : Nat) (hn : 0 < n)
    (observation : FKIsingSquareFullFaceNode n)
    (z : Option (FKIsingSquareFullFaceNode n))
    (hz : Not (faceDirichletBoundary n z))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n observation))
    (hhalf : ((n : Real) / 2) <= observation.1.1) :
    facePointPoissonBarrier n z (some observation) <=
      ((faceEndpointRadialShell n z : Real) +
          1 / isingFermionicGhostCoefficient) *
        (faceEndpointRadialShell n z : Real) / ((n : Real) / 2) := by
  cases z with
  | none =>
      exact False.elim (hz (by
        simp [faceDirichletBoundary, isingFiniteGhostBoundaryWith]))
  | some c =>
      have hobservation : Not (faceDirichletBoundary n (some observation)) := by
        simpa [faceDirichletBoundary, isingFiniteGhostBoundaryWith] using hfixed
      unfold facePointPoissonBarrier
      rw [isingFiniteWeightedPointPoissonBarrier_comm
        (faceGhostGraph n) (faceGhostConductance n)
        (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
        (faceGhostConductance_pos_of_adj n)
        (faceGhost_reaches_boundary n)
        (isingFiniteGhostConductance_comm
          (fkIsingSquareFullFaceGraph n)
          (isingFermionicGhostRate
            (fkIsingSquareFullFaceGhostMultiplicity n)))
        (some c) (some observation) hz hobservation]
      have hdistance : (0 : Real) < (n : Real) / 2 := by positivity
      have hleft : 0 < observation.1.1 := by
        by_contra h
        have hzcol : observation.1.1 = 0 := Nat.eq_zero_of_not_pos h
        simp [hzcol] at hhalf
        linarith
      have hrecip : 0 <= 1 / isingFermionicGhostCoefficient :=
        one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le
      by_cases hlower : c.2.1 <= 2 * n - 1 - c.2.1
      · apply facePointPoissonBarrier_le_lowerLeftRadius
          n (faceEndpointRadialShell n (some c)) ((n : Real) / 2)
          observation c hfixed hleft
        · simp [faceEndpointRadialShell, min_eq_left hlower]
        · exact hdistance
        · have hrow : 0 <= (observation.2.1 : Real) := by positivity
          linarith
      · have hupper : 2 * n - 1 - c.2.1 <= c.2.1 := by omega
        apply facePointPoissonBarrier_le_upperLeftRadius
          n (faceEndpointRadialShell n (some c)) ((n : Real) / 2)
          observation c hfixed hleft
        · simp [faceEndpointRadialShell, min_eq_right hupper]
        · exact hdistance
        · have hrow : 0 <=
              ((2 * n - 1 - observation.2.1 : Nat) : Real) := by
            positivity
          linarith



theorem vertexPointPoissonBarrier_le_endpointRadialQuadratic_of_halfColumn
    (n : Nat) (hn : 0 < n)
    (observation : FKIsingSquareFullVertexNode n)
    (z : Option (FKIsingSquareFullVertexNode n))
    (hz : Not (vertexDirichletBoundary n z))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n observation))
    (hright : observation.1 0 < (n : Int))
    (hbottom : -(n : Int) < observation.1 1)
    (htop : observation.1 1 < (n : Int))
    (hhalf : ((n : Real) / 2) <=
      fullVertexColumnIndex n observation) :
    vertexPointPoissonBarrier n z (some observation) <=
      endpointRadialGreenConstant *
        ((vertexEndpointRadialShell n z + 1 : Nat) : Real) ^ 2 /
          (n : Real) := by
  exact (vertexPointPoissonBarrier_le_endpointRadial_of_halfColumn
    n hn observation z hz hfixed hright hbottom htop hhalf).trans
      (endpointRadial_product_div_half_le n
        (vertexEndpointRadialShell n z) hn)


theorem facePointPoissonBarrier_le_endpointRadialQuadratic_of_halfColumn
    (n : Nat) (hn : 0 < n)
    (observation : FKIsingSquareFullFaceNode n)
    (z : Option (FKIsingSquareFullFaceNode n))
    (hz : Not (faceDirichletBoundary n z))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n observation))
    (hhalf : ((n : Real) / 2) <= observation.1.1) :
    facePointPoissonBarrier n z (some observation) <=
      endpointRadialGreenConstant *
        ((faceEndpointRadialShell n z + 1 : Nat) : Real) ^ 2 /
          (n : Real) := by
  have h := facePointPoissonBarrier_le_endpointRadial_of_halfColumn
    n hn observation z hz hfixed hhalf
  calc
    facePointPoissonBarrier n z (some observation) <=
        ((faceEndpointRadialShell n z : Real) +
            1 / isingFermionicGhostCoefficient) *
          (faceEndpointRadialShell n z : Real) / ((n : Real) / 2) := h
    _ = (faceEndpointRadialShell n z : Real) *
          ((faceEndpointRadialShell n z : Real) +
            1 / isingFermionicGhostCoefficient) / ((n : Real) / 2) := by
      ring
    _ <= endpointRadialGreenConstant *
          ((faceEndpointRadialShell n z + 1 : Nat) : Real) ^ 2 /
            (n : Real) :=
      endpointRadial_product_div_half_le n
        (faceEndpointRadialShell n z) hn

private theorem endpointRadial_quartic_mul_quadratic
    (n r : Nat) (hn : 0 < n) (R : Real) :
    (R / (((r + 1 : Nat) : Real) ^ 4)) *
        (endpointRadialGreenConstant *
          (((r + 1 : Nat) : Real) ^ 2) / (n : Real)) =
      (R * endpointRadialGreenConstant) /
        ((n : Real) * (((r + 1 : Nat) : Real) ^ 2)) := by
  have hnR : (n : Real) ≠ 0 := by exact_mod_cast hn.ne'
  have hr : (((r + 1 : Nat) : Real)) ≠ 0 := by positivity
  field_simp [hnR, hr]




theorem vertexSpatialTargetResidualPotential_le_endpointRadialHarmonic_of_residualDecay
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real)
    (observation : FKIsingSquareFullVertexNode n)
    (R : Real) (hR : 0 <= R)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n observation))
    (hright : observation.1 0 < (n : Int))
    (hbottom : -(n : Int) < observation.1 1)
    (htop : observation.1 1 < (n : Int))
    (hhalf : ((n : Real) / 2) <=
      fullVertexColumnIndex n observation)
    (hresidual : forall z,
      vertexSpatialTargetResidual n target z <=
        R / (((vertexEndpointRadialShell n z + 1 : Nat) : Real) ^ 4)) :
    vertexSpatialTargetResidualPotential n target (some observation) <=
      (R * endpointRadialGreenConstant) * 3 *
        (harmonic (3 * n + 1) : Real) / (n : Real) := by
  apply vertexSpatialTargetResidualPotential_le_endpointRadialHarmonic
    n hn target (some observation) (R * endpointRadialGreenConstant)
    (mul_nonneg hR endpointRadialGreenConstant_nonneg)
  intro z
  by_cases hz : vertexDirichletBoundary n z
  · have hzero : vertexSpatialTargetResidual n target z = 0 := by
      simp [vertexSpatialTargetResidual, hz]
    rw [hzero, zero_mul]
    exact div_nonneg
      (mul_nonneg hR endpointRadialGreenConstant_nonneg)
      (mul_nonneg (Nat.cast_nonneg _)
        (sq_nonneg (((vertexEndpointRadialShell n z + 1 : Nat) : Real))))
  · have hgreen :=
      vertexPointPoissonBarrier_le_endpointRadialQuadratic_of_halfColumn
        n hn observation z hz hfixed hright hbottom htop hhalf
    have hgreen0 : 0 <= vertexPointPoissonBarrier n z (some observation) := by
      unfold vertexPointPoissonBarrier
      exact isingFiniteWeightedPointPoissonBarrier_nonneg
        (vertexGhostGraph n) (vertexGhostConductance n)
        (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
        (vertexGhostConductance_pos_of_adj n)
        (vertexGhost_reaches_boundary n) z (some observation)
    calc
      vertexSpatialTargetResidual n target z *
          vertexPointPoissonBarrier n z (some observation) <=
        (R / (((vertexEndpointRadialShell n z + 1 : Nat) : Real) ^ 4)) *
          (endpointRadialGreenConstant *
            (((vertexEndpointRadialShell n z + 1 : Nat) : Real) ^ 2) /
              (n : Real)) := by
        apply mul_le_mul (hresidual z) hgreen hgreen0
        positivity
      _ = (R * endpointRadialGreenConstant) /
          ((n : Real) *
            (((vertexEndpointRadialShell n z + 1 : Nat) : Real) ^ 2)) :=
        endpointRadial_quartic_mul_quadratic n
          (vertexEndpointRadialShell n z) hn R


theorem faceSpatialTargetResidualPotential_le_endpointRadialHarmonic_of_residualDecay
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real)
    (observation : FKIsingSquareFullFaceNode n)
    (R : Real) (hR : 0 <= R)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n observation))
    (hhalf : ((n : Real) / 2) <= observation.1.1)
    (hresidual : forall z,
      faceSpatialTargetResidual n target z <=
        R / (((faceEndpointRadialShell n z + 1 : Nat) : Real) ^ 4)) :
    faceSpatialTargetResidualPotential n target (some observation) <=
      (R * endpointRadialGreenConstant) * 3 *
        (harmonic (3 * n + 1) : Real) / (n : Real) := by
  apply faceSpatialTargetResidualPotential_le_endpointRadialHarmonic
    n hn target (some observation) (R * endpointRadialGreenConstant)
    (mul_nonneg hR endpointRadialGreenConstant_nonneg)
  intro z
  by_cases hz : faceDirichletBoundary n z
  · have hzero : faceSpatialTargetResidual n target z = 0 := by
      simp [faceSpatialTargetResidual, hz]
    rw [hzero, zero_mul]
    exact div_nonneg
      (mul_nonneg hR endpointRadialGreenConstant_nonneg)
      (mul_nonneg (Nat.cast_nonneg _)
        (sq_nonneg (((faceEndpointRadialShell n z + 1 : Nat) : Real))))
  · have hgreen :=
      facePointPoissonBarrier_le_endpointRadialQuadratic_of_halfColumn
        n hn observation z hz hfixed hhalf
    have hgreen0 : 0 <= facePointPoissonBarrier n z (some observation) := by
      unfold facePointPoissonBarrier
      exact isingFiniteWeightedPointPoissonBarrier_nonneg
        (faceGhostGraph n) (faceGhostConductance n)
        (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
        (faceGhostConductance_pos_of_adj n)
        (faceGhost_reaches_boundary n) z (some observation)
    calc
      faceSpatialTargetResidual n target z *
          facePointPoissonBarrier n z (some observation) <=
        (R / (((faceEndpointRadialShell n z + 1 : Nat) : Real) ^ 4)) *
          (endpointRadialGreenConstant *
            (((faceEndpointRadialShell n z + 1 : Nat) : Real) ^ 2) /
              (n : Real)) := by
        apply mul_le_mul (hresidual z) hgreen hgreen0
        positivity
      _ = (R * endpointRadialGreenConstant) /
          ((n : Real) *
            (((faceEndpointRadialShell n z + 1 : Nat) : Real) ^ 2)) :=
        endpointRadial_quartic_mul_quadratic n
          (faceEndpointRadialShell n z) hn R

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
