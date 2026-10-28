/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowRootsData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMatrix
public import Mathlib.Tactic.Module

/-! The original eight short directions give the genuine orthogonal matrix projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The eight actual short directions as real physical row vectors. -/
def generatedNinthLowRootMatrix : Matrix (Fin 8) (Fin 24) ℝ :=
  fun r i => (generatedNinthLowRootCoordinates r i : ℝ)

/-- The real short-direction Gram matrix is exactly twice identity. -/
theorem generatedNinth_low_root_real_gram :
    generatedNinthLowRootMatrix * generatedNinthLowRootMatrix.transpose = (2 : ℝ) • 1 := by
  ext r s
  have h : (∑ i : Fin 24, (generatedNinthLowRootCoordinates r i : ℝ) *
      (generatedNinthLowRootCoordinates s i : ℝ)) = if r = s then 2 else 0 := by
    exact_mod_cast generatedNinth_low_root_gram r s
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, generatedNinthLowRootMatrix,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] using h

/-- The genuine orthogonal projection onto the span of the eight original short lines. -/
def generatedNinthLowProjection : Matrix (Fin 24) (Fin 24) ℝ :=
  (1 / 2 : ℝ) • (generatedNinthLowRootMatrix.transpose * generatedNinthLowRootMatrix)

/-- This actual short-line projection is idempotent. -/
theorem generatedNinth_low_projection_square :
    generatedNinthLowProjection * generatedNinthLowProjection = generatedNinthLowProjection := by
  let C := generatedNinthLowRootMatrix
  have h : (C.transpose * C) * (C.transpose * C) = (2 : ℝ) • (C.transpose * C) := by
    calc
      _ = C.transpose * ((C * C.transpose) * C) := by simp only [Matrix.mul_assoc]
      _ = C.transpose * ((2 : ℝ) • C) := by
        rw [generatedNinth_low_root_real_gram, Matrix.smul_mul, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_smul]
  change ((1 / 2 : ℝ) • (C.transpose * C)) * ((1 / 2 : ℝ) • (C.transpose * C)) = _
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, smul_smul]
  norm_num [generatedNinthLowProjection, C]

/-- The short-line projection is symmetric in the actual real matrix coordinates. -/
theorem generatedNinth_low_projection_symmetric :
    generatedNinthLowProjection.transpose = generatedNinthLowProjection := by
  simp only [generatedNinthLowProjection, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- The whole actual ninth matrix is three eighths identity minus one eighth of this projection. -/
theorem generatedNinth_matrix_projection :
    (griessConwayEncode generatedNinthAxis).1 =
      (3 / 8 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) -
        (1 / 8 : ℝ) • generatedNinthLowProjection := by
  rw [generatedNinth_axis_matrix]
  ext i j
  have h : (generatedNinthMatrixNumerator i j : ℝ) =
      12 * (if i = j then (1 : ℝ) else 0) -
        2 * ∑ r : Fin 8, (generatedNinthLowRootCoordinates r i : ℝ) *
          (generatedNinthLowRootCoordinates r j : ℝ) := by
    exact_mod_cast generatedNinth_low_root_matrix i j
  simp only [generatedNinthAxisMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    generatedNinthLowProjection, Matrix.mul_apply, Matrix.transpose_apply,
    generatedNinthLowRootMatrix, smul_eq_mul]
  rw [h]
  ring

/-- The lower projection is recovered directly from the actual prototype matrix. -/
theorem generatedNinth_low_projection_recover :
    (3 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) -
      (8 : ℝ) • (griessConwayEncode generatedNinthAxis).1 = generatedNinthLowProjection := by
  rw [generatedNinth_matrix_projection]
  module

/-- Actual spatial matrix fixation is exactly fixation of the original eight-line projection. -/
theorem generatedNinth_matrix_stabilizer_iff (g : leechIsomSubgroup) :
    conwayMatrixAction g (griessConwayEncode generatedNinthAxis).1 =
        (griessConwayEncode generatedNinthAxis).1 ↔
      conwayMatrixAction g generatedNinthLowProjection = generatedNinthLowProjection := by
  constructor
  · intro h
    rw [← generatedNinth_low_projection_recover]
    rw [map_sub, map_smul, map_smul, conwayMatrixAction_one, h]
  · intro h
    rw [generatedNinth_matrix_projection]
    rw [map_sub, map_smul, map_smul, conwayMatrixAction_one, h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
