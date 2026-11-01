/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates

/-! The actual sixth prototype's matrix diagonal follows from its norm-eight spatial image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Before exterior triality, the actual matrix is the transported norm-eight outer. -/
theorem generatedSixth_middle_matrix :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedSixthLocalFiber)
      generatedOddAxis)).1 =
        (1 / 4 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) +
          (1 / 4 : ℝ) • generatedNormEightLineMatrix generatedSixthNormEightVector := by
  rw [generatedFourth_local_matrix]
  unfold generatedOddAxis
  rw [generatedNormEightLine_odd_matrix, map_add, map_smul, map_smul,
    conwayMatrixAction_one, ← generatedNormEightLineMatrix_action]
  rfl

/-- Every actual diagonal coordinate has the exact integer-square formula. -/
theorem generatedSixth_matrix_diagonal_data (i : Fin 24) :
    (griessConwayEncode generatedSixthAxis).1 i i =
      1 / 4 + (generatedSixthNormEightVectorData 8 i : ℝ) ^ 2 / 32 := by
  rw [generatedSixthAxis_local_expression, generatedFourth_triality_matrix_diagonal,
    generatedSixth_middle_matrix]
  have hv : generatedNormEightVector generatedSixthNormEightVector i =
      (generatedSixthNormEightVectorData 8 i : ℝ) / Real.sqrt 8 := by
    simp only [generatedNormEightVector, generatedSixthNormEightVector_val,
      leechCoordinateEmbedding]
    rfl
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, ite_true,
    smul_eq_mul, generatedNormEightLineMatrix, Matrix.vecMulVec_apply, mul_one]
  rw [hv, ← pow_two, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  ring

/-- The original diagonal singles out coordinates sixteen, seventeen and nineteen. -/
theorem generatedSixth_matrix_diagonal (i : Fin 24) :
    (griessConwayEncode generatedSixthAxis).1 i i =
      if i = 19 then (33 / 32 : ℝ) else
        if i = 16 ∨ i = 17 then 17 / 32 else 9 / 32 := by
  rw [generatedSixth_matrix_diagonal_data]
  fin_cases i <;> norm_num [generatedSixthNormEightVectorData]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
