/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMatrixRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorAction

/-! Actual three-bases fixation of the original fifth matrix watermark. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check the 576 actual tetrad matrix entries and the selected original octad mask.
/-- The original integer Xi matrix commutes with the selected coordinate projection. -/
theorem generatedFifth_xi_projection_integer_certificate : ∀ i j : Fin 24,
    co1XiNumerator i j * (if Nat.testBit 0x0f000f j.val then (1 : ℤ) else 0) =
      (if Nat.testBit 0x0f000f i.val then (1 : ℤ) else 0) * co1XiNumerator i j := by
  decide +kernel

/-- The actual physical Xi matrix commutes with the literal selected E8 projection. -/
theorem generatedFifth_xi_projection_commute :
    leechIsomMatrix co1XiIsometry *
      Matrix.diagonal (fun i => if golayOctadWord generatedFifthFlagOctad i = 0
        then (0 : ℝ) else 1) =
      Matrix.diagonal (fun i => if golayOctadWord generatedFifthFlagOctad i = 0
        then (0 : ℝ) else 1) * leechIsomMatrix co1XiIsometry := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, generatedFifth_flag_word_coordinate]
  change (xiSpinLocalFiber.val.2.val (Pi.single j 1) i) * _ =
    _ * (xiSpinLocalFiber.val.2.val (Pi.single j 1) i)
  rw [generatedFifth_xi_spatial_unit]
  have hh := congrArg (fun z : ℤ => (z : ℝ) / 2)
    (generatedFifth_xi_projection_integer_certificate i j)
  cases hi : Nat.testBit 0x0f000f i.val <;>
    cases hj : Nat.testBit 0x0f000f j.val <;>
      norm_num [hi, hj, golayBooleanCast] at hh ⊢ <;> linarith

/-- The actual Xi physical isometry fixes the selected projection by its genuine orthogonality. -/
theorem generatedFifth_xi_projection_fixed :
    conwayMatrixAction co1XiIsometry
      (Matrix.diagonal (fun i => if golayOctadWord generatedFifthFlagOctad i = 0
        then (0 : ℝ) else 1)) =
      Matrix.diagonal (fun i => if golayOctadWord generatedFifthFlagOctad i = 0
        then (0 : ℝ) else 1) := by
  have ho : leechIsomMatrix co1XiIsometry *
      (leechIsomMatrix co1XiIsometry).transpose = 1 :=
    mul_eq_one_comm.mp (leechIsomMatrix_transpose_mul co1XiIsometry)
  rw [conwayMatrixAction_eq_conjugate, generatedFifth_xi_projection_commute,
    Matrix.mul_assoc, ho, Matrix.mul_one]

/-- The actual Xi isometry fixes the exact original fifth matrix, with no spatial assumption. -/
theorem generatedFifth_xi_matrix_fixed :
    conwayMatrixAction co1XiIsometry (griessConwayEncode generatedFifthAxis).1 =
      (griessConwayEncode generatedFifthAxis).1 := by
  rw [generatedFifth_matrix_affine_projection, map_add, map_smul, map_smul,
    conwayMatrixAction_one, generatedFifth_xi_projection_fixed]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
