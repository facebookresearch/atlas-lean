/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthDiagonal

/-! The complete actual local fifth-image matrix from its original signed rational frame columns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original frame columns give the exact integral middle matrix numerator. -/
def generatedNinthMiddleMatrixInteger (i j : Fin 24) : ℤ :=
  ∑ k : Fin 24, (if Nat.testBit 0x0f000f k.val then (2 : ℤ) else 1) *
    generatedNinthFrameVectorData 9 k i * generatedNinthFrameVectorData 9 k j

/-- Every actual middle matrix entry is its exact original integer numerator divided by256. -/
theorem generatedNinth_middle_matrix_integer (i j : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).1 i j = (generatedNinthMiddleMatrixInteger i j : ℝ) / 256 := by
  rw [generatedFourth_local_matrix, generatedFifth_matrix]
  rw [← Matrix.toBilin'_single (conwayMatrixAction generatedNinthLocalFiber.val.2
    (Matrix.diagonal (fun k : Fin 24 =>
      if Nat.testBit 0x0f000f k.val then (1 / 2 : ℝ) else 1 / 4))) i j,
    conwayMatrixAction_pairing]
  change Matrix.toBilin' _
    ((generatedNinthLocalFiber.val.2⁻¹).val (Pi.single i 1))
    ((generatedNinthLocalFiber.val.2⁻¹).val (Pi.single j 1)) = _
  rw [← leechIsomMatrix_mulVec (generatedNinthLocalFiber.val.2⁻¹),
    ← leechIsomMatrix_mulVec (generatedNinthLocalFiber.val.2⁻¹)]
  simp only [Matrix.mulVec_single, Matrix.toBilin'_apply, Matrix.diagonal_apply,
    MulOpposite.op_one, one_smul, Matrix.col_apply]
  simp_rw [generatedNinth_inverse_matrix_coordinate]
  simp only [generatedNinthMiddleMatrixInteger, Int.cast_sum, Int.cast_mul, Int.cast_ite,
    Int.cast_ofNat]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hb : Nat.testBit 0x0f000f k.val = true
  · simp [hb]
    ring
  · simp [hb]
    ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
