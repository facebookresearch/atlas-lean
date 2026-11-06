/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisTriality

/-! The full transported middle projector and its actual final pair-short coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- Sixteen times the actual middle projector, including all off-diagonal entries. -/
def generatedFifthMiddleProjectorNumerator (i j : Fin 24) : ℤ :=
  ∑ k : Fin 24, if Nat.testBit 0xcccc00 k.val then
    generatedFifthInverseNumerator k i * generatedFifthInverseNumerator k j else 0

/-- The original inverse spatial certificate determines every transported projector entry. -/
theorem generatedFifth_middle_projector_coordinate (i j : Fin 24) :
    conwayMatrixAction generatedFifthLocalFiber.val.2
      (Matrix.diagonal (fun k : Fin 24 => if Nat.testBit 0xcccc00 k.val then 1 else 0)) i j =
        (generatedFifthMiddleProjectorNumerator i j : ℝ) / 16 := by
  rw [← Matrix.toBilin'_single (conwayMatrixAction generatedFifthLocalFiber.val.2
    (Matrix.diagonal (fun k : Fin 24 => if Nat.testBit 0xcccc00 k.val then (1 : ℝ) else 0)))
    i j, conwayMatrixAction_pairing]
  change Matrix.toBilin' _
    ((generatedFifthLocalFiber⁻¹).val.2.val (Pi.single i 1))
    ((generatedFifthLocalFiber⁻¹).val.2.val (Pi.single j 1)) = _
  rw [generatedFifth_inverse_spatial_action, generatedFifth_inverse_spatial_action]
  simp only [Matrix.mulVec_single, Matrix.toBilin'_apply, Matrix.diagonal_apply,
    MulOpposite.op_one, one_smul, Matrix.col_apply]
  simp_rw [generatedFifth_inverse_matrix_entry]
  simp only [generatedFifthMiddleProjectorNumerator, Int.cast_sum, Int.cast_ite,
    Int.cast_mul, Int.cast_zero, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hb : Nat.testBit 0xcccc00 k.val = true
  · simp [hb, mul_ite, ite_mul]
    ring
  · simp [hb]

/-- The complete actual middle matrix is the certified projector divided by sixteen. -/
theorem generatedFifth_middle_matrix_entry (i j : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedFifthLocalFiber)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).1 i j =
        (generatedFifthMiddleProjectorNumerator i j : ℝ) / 16 := by
  rw [generatedFourth_local_matrix, generatedAxis_triality_octad_matrix,
    generatedFourthOctad_mask]
  exact generatedFifth_middle_projector_coordinate i j

/-- The final minus-pair coordinate is the actual transported off-diagonal projector entry. -/
theorem generatedFifth_final_pair_minus (p : Fin 276) :
    (griessConwayEncode generatedFifthAxis).2.1 (Sum.inl (0, p)) =
      (generatedFifthMiddleProjectorNumerator
        (griessCoordinatePair p).1 (griessCoordinatePair p).2 : ℝ) / 16 := by
  rw [generatedFifthAxis_local_expression, generatedFourthQShortBasis_triality_pair_minus,
    generatedFourth_local_short, generatedFifth_middle_pair_zero,
    generatedFifth_middle_pair_zero, generatedFifth_middle_matrix_entry]
  ring

/-- The final plus-pair coordinate has the opposite actual projector sign. -/
theorem generatedFifth_final_pair_plus (p : Fin 276) :
    (griessConwayEncode generatedFifthAxis).2.1 (Sum.inl (1, p)) =
      -(generatedFifthMiddleProjectorNumerator
        (griessCoordinatePair p).1 (griessCoordinatePair p).2 : ℝ) / 16 := by
  rw [generatedFifthAxis_local_expression, generatedFourthQShortBasis_triality_pair_plus,
    generatedFourth_local_short, generatedFifth_middle_pair_zero,
    generatedFifth_middle_pair_zero, generatedFifth_middle_matrix_entry]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
