/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthTensor
public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortSupport

/-! Exact rational matrix and signed pair coefficients of the genuine fifth prototype. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Exact rational entries of the actual middle octad projector. -/
def generatedAxisGlobalFifthMiddleMatrixQ (i j : Fin 24) : ℚ :=
  (∑ t : Fin 24, if Nat.testBit 0xcccc00 t.val then
    (generatedFifthInverseNumerator t i : ℚ) * (generatedFifthInverseNumerator t j : ℚ)
    else 0) / 16

/-- Every middle real matrix entry equals its explicit rational projector entry. -/
theorem generatedAxisGlobalFifthMiddleMatrix_entry (i j : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedFifthLocalFiber)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).1 i j =
      (generatedAxisGlobalFifthMiddleMatrixQ i j : ℝ) := by
  rw [generatedFourth_local_matrix, generatedAxis_triality_octad_matrix,
    generatedFourthOctad_mask]
  rw [← Matrix.toBilin'_single (conwayMatrixAction generatedFifthLocalFiber.val.2
    (Matrix.diagonal (fun t : Fin 24 => if Nat.testBit 0xcccc00 t.val then 1 else 0))) i j,
    conwayMatrixAction_pairing]
  change Matrix.toBilin' _
    ((generatedFifthLocalFiber⁻¹).val.2.val (Pi.single i 1))
    ((generatedFifthLocalFiber⁻¹).val.2.val (Pi.single j 1)) = _
  rw [generatedFifth_inverse_spatial_action, generatedFifth_inverse_spatial_action]
  simp only [Matrix.mulVec_single, Matrix.toBilin'_apply, Matrix.diagonal_apply,
    MulOpposite.op_one, one_smul, Matrix.col_apply]
  simp_rw [generatedFifth_inverse_matrix_entry]
  rw [generatedAxisGlobalFifthMiddleMatrixQ]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hb : Nat.testBit 0xcccc00 t.val = true
  · simp [hb, mul_ite, ite_mul]
    ring
  · simp [hb]

/-- The actual minus-pair short entry is the exact rational middle matrix entry. -/
theorem generatedAxisGlobalFifthRaw_pair_minus (p : Fin 276) :
    (griessConwayEncode generatedFifthAxis).2.1 (Sum.inl (0, p)) =
      (generatedAxisGlobalFifthMiddleMatrixQ
        (griessCoordinatePair p).1 (griessCoordinatePair p).2 : ℝ) := by
  rw [generatedFifthAxis_local_expression, generatedFourthQShortBasis_triality_pair_minus,
    generatedAxisGlobalFifthMiddleMatrix_entry, generatedFourth_local_short,
    generatedFifth_middle_pair_zero, generatedFifth_middle_pair_zero]
  ring

/-- The actual plus-pair short entry is the negative rational middle matrix entry. -/
theorem generatedAxisGlobalFifthRaw_pair_plus (p : Fin 276) :
    (griessConwayEncode generatedFifthAxis).2.1 (Sum.inl (1, p)) =
      -(generatedAxisGlobalFifthMiddleMatrixQ
        (griessCoordinatePair p).1 (griessCoordinatePair p).2 : ℝ) := by
  rw [generatedFifthAxis_local_expression, generatedFourthQShortBasis_triality_pair_plus,
    generatedAxisGlobalFifthMiddleMatrix_entry, generatedFourth_local_short,
    generatedFifth_middle_pair_zero, generatedFifth_middle_pair_zero]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
