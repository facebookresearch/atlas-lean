/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates

/-! The actual seventh prototype's matrix diagonal follows from its norm-eight spatial image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Before exterior triality, the actual matrix is the transported norm-eight outer. -/
theorem generatedSeventh_middle_matrix :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedSeventhLocalFiber)
      generatedOddAxis)).1 =
        (1 / 4 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) +
          (1 / 4 : ℝ) • generatedNormEightLineMatrix generatedSeventhNormEightVector := by
  rw [generatedFourth_local_matrix]
  unfold generatedOddAxis
  rw [generatedNormEightLine_odd_matrix, map_add, map_smul, map_smul,
    conwayMatrixAction_one, ← generatedNormEightLineMatrix_action]
  rfl

/-- Every actual diagonal coordinate has the exact integer-square formula. -/
theorem generatedSeventh_matrix_diagonal_data (i : Fin 24) :
    (griessConwayEncode generatedSeventhAxis).1 i i =
      1 / 4 + (generatedSeventhNormEightVectorData 7 i : ℝ) ^ 2 / 32 := by
  rw [generatedSeventhAxis_local_expression, generatedFourth_triality_matrix_diagonal,
    generatedSeventh_middle_matrix]
  have hv : generatedNormEightVector generatedSeventhNormEightVector i =
      (generatedSeventhNormEightVectorData 7 i : ℝ) / Real.sqrt 8 := by
    simp only [generatedNormEightVector, generatedSeventhNormEightVector_val,
      leechCoordinateEmbedding]
    rfl
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, ite_true,
    smul_eq_mul, generatedNormEightLineMatrix, Matrix.vecMulVec_apply, mul_one]
  rw [hv, ← pow_two, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  ring

/-- The actual matrix diagonal distinguishes the five original magnitude-three coordinates. -/
theorem generatedSeventh_matrix_diagonal (i : Fin 24) :
    (griessConwayEncode generatedSeventhAxis).1 i i =
      if i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 18 then (17 / 32 : ℝ)
        else 9 / 32 := by
  rw [generatedSeventh_matrix_diagonal_data]
  fin_cases i <;> norm_num [generatedSeventhNormEightVectorData]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
