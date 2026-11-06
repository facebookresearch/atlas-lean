/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthSpatial

/-! The actual diagonal coordinates of the fifth locally transported octad matrix.
All numerical entries come from the checked original integer matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators

/-- The real inverse matrix entry is the checked integer entry divided by four. -/
theorem generatedFifth_inverse_matrix_entry (i j : Fin 24) :
    generatedFifthInverseMatrix i j = (generatedFifthInverseNumerator i j : ℝ) / 4 := by
  simp only [generatedFifthInverseMatrix, generatedFifthInverseMatrixQ, Matrix.map_apply]
  norm_num

/-- Actual congruence action on the selected octad projector has the certified diagonal. -/
theorem generatedFifth_projection_diagonal (i : Fin 24) :
    conwayMatrixAction generatedFifthLocalFiber.val.2
      (Matrix.diagonal (fun j : Fin 24 => if Nat.testBit 0xcccc00 j.val then 1 else 0)) i i =
        (generatedFifthProjectionDiagonal i : ℝ) / 16 := by
  rw [← Matrix.toBilin'_single (conwayMatrixAction generatedFifthLocalFiber.val.2
    (Matrix.diagonal (fun j : Fin 24 => if Nat.testBit 0xcccc00 j.val then 1 else 0))) i i,
    conwayMatrixAction_pairing]
  change Matrix.toBilin' _
    ((generatedFifthLocalFiber⁻¹).val.2.val (Pi.single i 1))
    ((generatedFifthLocalFiber⁻¹).val.2.val (Pi.single i 1)) = _
  rw [generatedFifth_inverse_spatial_action]
  simp only [Matrix.mulVec_single, Matrix.toBilin'_apply, Matrix.diagonal_apply]
  simp only [MulOpposite.op_one, one_smul, Matrix.col_apply]
  simp_rw [generatedFifth_inverse_matrix_entry]
  have hn : (∑ j : Fin 24, if Nat.testBit 0xcccc00 j.val then
      (generatedFifthInverseNumerator j i : ℝ) *
        (generatedFifthInverseNumerator j i : ℝ) else 0) =
      (generatedFifthProjectionDiagonal i : ℝ) := by
    exact_mod_cast generatedFifth_projection_diagonal_certificate i
  calc
    _ = (∑ j : Fin 24, if Nat.testBit 0xcccc00 j.val then
        (generatedFifthInverseNumerator j i : ℝ) *
          (generatedFifthInverseNumerator j i : ℝ) else 0) / 16 := by
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hb : Nat.testBit 0xcccc00 j.val = true
      · simp [hb, mul_ite, ite_mul]
        ring
      · simp [hb]
    _ = _ := by rw [hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
