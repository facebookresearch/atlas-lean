/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisPairData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every middle projector entry has its original exact integer numerator. -/
theorem generatedFourthQShortBasis_projection_entry (i j : Fin 24) :
    conwayMatrixAction generatedFourthLocalFiber.val.2
      (Matrix.diagonal (fun k : Fin 24 => if Nat.testBit 0xcccc00 k.val then 1 else 0)) i j =
        (generatedFourthQShortBasisProjectionNumerator i j : ℝ) / 16 := by
  rw [← Matrix.toBilin'_single (conwayMatrixAction generatedFourthLocalFiber.val.2
    (Matrix.diagonal (fun k : Fin 24 => if Nat.testBit 0xcccc00 k.val then 1 else 0))) i j,
    conwayMatrixAction_pairing]
  change Matrix.toBilin' _
    ((generatedFourthLocalFiber⁻¹).val.2.val (Pi.single i 1))
    ((generatedFourthLocalFiber⁻¹).val.2.val (Pi.single j 1)) = _
  rw [generatedFourth_inverse_spatial_action, generatedFourth_inverse_spatial_action]
  simp only [Matrix.mulVec_single, Matrix.toBilin'_apply, Matrix.diagonal_apply]
  simp only [MulOpposite.op_one, one_smul, Matrix.col_apply]
  simp_rw [generatedFourth_inverse_matrix_entry]
  have hn : (∑ k : Fin 24, if Nat.testBit 0xcccc00 k.val then
      (generatedFourthInverseNumerator k i : ℝ) *
        (generatedFourthInverseNumerator k j : ℝ) else 0) =
      (generatedFourthQShortBasisProjectionNumerator i j : ℝ) := by
    simp [generatedFourthQShortBasisProjectionNumerator, Int.cast_sum, Int.cast_ite]
  calc
    _ = (∑ k : Fin 24, if Nat.testBit 0xcccc00 k.val then
        (generatedFourthInverseNumerator k i : ℝ) *
          (generatedFourthInverseNumerator k j : ℝ) else 0) / 16 := by
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hb : Nat.testBit 0xcccc00 k.val = true
      · simp [hb, mul_ite, ite_mul]
        ring
      · simp [hb]
    _ = _ := by rw [hn]

/-- Every actual middle matrix coordinate has its verified original projector numerator. -/
theorem generatedFourthQShortBasis_middle_matrix (i j : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedFourthLocalFiber)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).1 i j =
        (generatedFourthQShortBasisProjectionNumerator i j : ℝ) / 16 := by
  rw [generatedFourth_local_matrix, generatedAxis_triality_octad_matrix, generatedFourthOctad_mask]
  exact generatedFourthQShortBasis_projection_entry i j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
