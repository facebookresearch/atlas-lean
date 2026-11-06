/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMatrix

/-! The genuine moving spatial lift preserves the whole actual seventh matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- A commutation check needs only two twenty-four-term sums per matrix entry.
private theorem numerator_commutes :
    generatedSeventhXiPlaneMatrixNumerator * generatedSeventhMatrixNumerator =
      generatedSeventhMatrixNumerator * generatedSeventhXiPlaneMatrixNumerator := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- The actual spatial matrix commutes with the entire original seventh matrix. -/
theorem generatedSeventhXiPlane_matrix_commutes :
    let A : Matrix (Fin 24) (Fin 24) ℝ := generatedSeventhAxisMatrix
    leechIsomMatrix generatedSeventhXiPlaneFiber.val.2 * A =
      A * leechIsomMatrix generatedSeventhXiPlaneFiber.val.2 := by
  dsimp only
  have h := congrArg (Int.castRingHom ℝ).mapMatrix numerator_commutes
  rw [map_mul, map_mul] at h
  simp only [RingHom.mapMatrix_apply] at h
  rw [generatedSeventhXiPlaneFiber_matrix, generatedSeventh_matrix_numerator_real]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  change (1 / 32 * (1 / 2) : ℝ) •
      (generatedSeventhXiPlaneMatrixNumerator.map (Int.castRingHom ℝ) *
        generatedSeventhMatrixNumerator.map (Int.castRingHom ℝ)) =
    (1 / 2 * (1 / 32) : ℝ) •
      (generatedSeventhMatrixNumerator.map (Int.castRingHom ℝ) *
        generatedSeventhXiPlaneMatrixNumerator.map (Int.castRingHom ℝ))
  rw [h, mul_comm (1 / 2 : ℝ) (1 / 32)]

/-- The corrected original local lift fixes the full actual seventh matrix block. -/
theorem generatedSeventhXiPlane_matrix_fixed :
    conwayMatrixAction generatedSeventhXiPlaneFiber.val.2 generatedSeventhAxisMatrix =
      generatedSeventhAxisMatrix := by
  rw [conwayMatrixAction_eq_conjugate, generatedSeventhXiPlane_matrix_commutes,
    Matrix.mul_assoc, mul_eq_one_comm.mp
      (leechIsomMatrix_transpose_mul generatedSeventhXiPlaneFiber.val.2), Matrix.mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
