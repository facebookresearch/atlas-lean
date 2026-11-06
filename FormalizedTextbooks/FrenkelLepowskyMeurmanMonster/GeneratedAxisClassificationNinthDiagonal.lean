/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpatial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthDiagonalData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMatrix

/-! Actual diagonal coordinates follow from original fifth-axis and frame certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual diagonal is the finite signed-source certificate divided by thirty-two. -/
theorem generatedNinth_matrix_diagonal (i : Fin 24) :
    (griessConwayEncode generatedNinthAxis).1 i i =
      (generatedNinthDiagonalNumerator i : ℝ) / 32 := by
  rw [generatedNinthAxis_local_expression, generatedFourth_triality_matrix_diagonal,
    generatedFourth_local_matrix, generatedFifth_matrix]
  rw [← Matrix.toBilin'_single (conwayMatrixAction generatedNinthLocalFiber.val.2
    (Matrix.diagonal (fun k : Fin 24 =>
      if Nat.testBit 0x0f000f k.val then (1 / 2 : ℝ) else 1 / 4))) i i,
    conwayMatrixAction_pairing]
  change Matrix.toBilin' _
    ((generatedNinthLocalFiber.val.2⁻¹).val (Pi.single i 1))
    ((generatedNinthLocalFiber.val.2⁻¹).val (Pi.single i 1)) = _
  rw [← leechIsomMatrix_mulVec (generatedNinthLocalFiber.val.2⁻¹)]
  simp only [Matrix.mulVec_single, Matrix.toBilin'_apply, Matrix.diagonal_apply,
    MulOpposite.op_one, one_smul, Matrix.col_apply]
  simp_rw [generatedNinth_inverse_matrix_coordinate]
  have hn : (∑ k : Fin 24, (if Nat.testBit 0x0f000f k.val then (2 : ℝ) else 1) *
      (generatedNinthFrameVectorData 9 k i : ℝ) *
        (generatedNinthFrameVectorData 9 k i : ℝ)) =
      8 * (generatedNinthDiagonalNumerator i : ℝ) := by
    exact_mod_cast generatedNinth_diagonal_certificate i
  calc
    _ = (∑ k : Fin 24, (if Nat.testBit 0x0f000f k.val then (2 : ℝ) else 1) *
        (generatedNinthFrameVectorData 9 k i : ℝ) *
          (generatedNinthFrameVectorData 9 k i : ℝ)) / 256 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hb : Nat.testBit 0x0f000f k.val = true
      · simp [hb]
        ring
      · simp [hb]
        ring
    _ = _ := by rw [hn]; ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
