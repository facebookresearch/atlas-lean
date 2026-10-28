/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthInverseSpatial

/-! The actual diagonal coordinates of the locally transported octad matrix.
All numerical entries come from the checked original integer matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators

/-- The real inverse matrix entry is the checked integer entry divided by four. -/
theorem generatedFourth_inverse_matrix_entry (i j : Fin 24) :
    generatedFourthInverseMatrix i j = (generatedFourthInverseNumerator i j : ℝ) / 4 := by
  simp only [generatedFourthInverseMatrix, generatedFourthInverseMatrixQ, Matrix.map_apply]
  norm_num

/-- Actual congruence action on the selected octad projector has the certified diagonal. -/
theorem generatedFourth_projection_diagonal (i : Fin 24) :
    conwayMatrixAction generatedFourthLocalFiber.val.2
      (Matrix.diagonal (fun j : Fin 24 => if Nat.testBit 0xcccc00 j.val then 1 else 0)) i i =
        (generatedFourthProjectionDiagonal i : ℝ) / 16 := by
  rw [← Matrix.toBilin'_single (conwayMatrixAction generatedFourthLocalFiber.val.2
    (Matrix.diagonal (fun j : Fin 24 => if Nat.testBit 0xcccc00 j.val then 1 else 0))) i i,
    conwayMatrixAction_pairing]
  change Matrix.toBilin' _
    ((generatedFourthLocalFiber⁻¹).val.2.val (Pi.single i 1))
    ((generatedFourthLocalFiber⁻¹).val.2.val (Pi.single i 1)) = _
  rw [generatedFourth_inverse_spatial_action]
  simp only [Matrix.mulVec_single, Matrix.toBilin'_apply, Matrix.diagonal_apply]
  simp only [MulOpposite.op_one, one_smul, Matrix.col_apply]
  simp_rw [generatedFourth_inverse_matrix_entry]
  have hn : (∑ j : Fin 24, if Nat.testBit 0xcccc00 j.val then
      (generatedFourthInverseNumerator j i : ℝ) *
        (generatedFourthInverseNumerator j i : ℝ) else 0) =
      (generatedFourthProjectionDiagonal i : ℝ) := by
    exact_mod_cast generatedFourth_projection_diagonal_certificate i
  calc
    _ = (∑ j : Fin 24, if Nat.testBit 0xcccc00 j.val then
        (generatedFourthInverseNumerator j i : ℝ) *
          (generatedFourthInverseNumerator j i : ℝ) else 0) / 16 := by
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hb : Nat.testBit 0xcccc00 j.val = true
      · simp [hb, mul_ite, ite_mul]
        ring
      · simp [hb]
    _ = _ := by rw [hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
