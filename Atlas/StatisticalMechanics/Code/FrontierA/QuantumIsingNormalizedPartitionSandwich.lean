/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingFiniteSpectralBridge
import Code.FrontierA.QuantumIsingSectorBounds
import Code.FrontierA.QuantumIsingArfSandwich
import Code.FrontierA.QuantumIsingThermodynamicLimit









namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def quantumIsingNormalizedDiagonalPartition
    (beta h : Real) (L : Nat) : Real :=
  Real.exp (-quantumIsingVerticalCoupling beta h L) ^ (L * L) *
    quantumIsingClassicalCylinderPartition beta h L L

theorem quantumIsingNormalizedDiagonalPartition_pos
    (beta h : Real) (L : Nat) [Fact (2 < L)] :
    0 < quantumIsingNormalizedDiagonalPartition beta h L := by
  unfold quantumIsingNormalizedDiagonalPartition
  exact mul_pos (pow_pos (Real.exp_pos _) _)
    (quantumIsingClassicalCylinderPartition_pos beta h L L)

theorem quantumIsingNormalizedSpinSector_norm_le_partition
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (hbeta : 0 < beta) (hx : 0 < beta * h / (2 * L))
    (hx1 : beta * h / (2 * L) < 1)
    (a b : Fin 2) :
    ‖quantumIsingNormalizedSpinSector beta h L a b‖ ≤
      quantumIsingNormalizedDiagonalPartition beta h L := by
  let E := Real.exp (-quantumIsingVerticalCoupling beta h L)
  let C := Real.cosh (beta / (4 * L)) *
    Real.cosh (quantumIsingVerticalCoupling beta h L)
  let x := Real.tanh (beta / (4 * L))
  let y := Real.tanh (quantumIsingVerticalCoupling beta h L)
  let S := ons_weightedSpinCharacterSum L
    (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) a b
  let Q := inhomogeneousEvenSubgraphSum (onsTorusGraph L)
    (fun edge => if squareTorusHorizontalEdge L edge then x else y)
  have hJ : 0 < quantumIsingVerticalCoupling beta h L := by
    unfold quantumIsingVerticalCoupling
    have hlog : Real.log (beta * h / (2 * L)) < 0 := Real.log_neg hx hx1
    nlinarith
  have hx0 : 0 ≤ x := by
    dsimp [x]
    rw [Real.tanh_eq_sinh_div_cosh]
    positivity
  have hy0 : 0 ≤ y := by
    dsimp [y]
    rw [Real.tanh_eq_sinh_div_cosh]
    positivity
  have hSQ : ‖S‖ ≤ Q :=
    anisotropicSquare_weightedSpin_norm_le_evenSubgraphSum L hx0 hy0 a b
  have hZ : quantumIsingNormalizedDiagonalPartition beta h L =
      (2 * E * C) ^ (L * L) * Q := by
    unfold quantumIsingNormalizedDiagonalPartition
    rw [quantumIsingClassicalCylinderPartition_highTemperature]
    dsimp [E, C, Q, x, y]
    unfold quantumIsingSquareTorusTanhWeight
    rw [mul_pow, mul_pow]
    ring
  rw [hZ]
  unfold quantumIsingNormalizedSpinSector
  change ‖(((2 * E * C) ^ (L * L) : Real) : Complex) * S‖ ≤
    (2 * E * C) ^ (L * L) * Q
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by positivity) _)]
  exact mul_le_mul_of_nonneg_left hSQ (pow_nonneg (by positivity) _)



theorem quantumIsingNormalizedDiagonalPartition_log_sandwich
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (hbeta : 0 < beta) (hx : 0 < beta * h / (2 * L))
    (hx1 : beta * h / (2 * L) < 1) :
    Real.log
        (arfSectorNormMax (quantumIsingNormalizedSpinSector beta h L)) ≤
      Real.log (quantumIsingNormalizedDiagonalPartition beta h L) ∧
    Real.log (quantumIsingNormalizedDiagonalPartition beta h L) ≤
      Real.log
          (arfSectorNormMax (quantumIsingNormalizedSpinSector beta h L)) +
        Real.log 2 := by
  apply arfSector_log_sandwich
  · exact quantumIsingNormalizedDiagonalPartition_pos beta h L
  · intro a b
    exact quantumIsingNormalizedSpinSector_norm_le_partition
      beta h L hbeta hx hx1 a b
  · simpa [quantumIsingNormalizedDiagonalPartition] using
      two_mul_quantumIsingNormalizedClassicalPartition_eq_sectors beta h L

end StatMech.FrontierA
