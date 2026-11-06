/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates

/-! The exact original diagonal coordinates of the eighth prototype. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Before exterior triality, the actual matrix is the transported norm-eight outer. -/
theorem generatedEighth_middle_matrix :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedEighthLocalFiber)
      generatedOddAxis)).1 =
        (1 / 4 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) +
          (1 / 4 : ℝ) • generatedNormEightLineMatrix generatedEighthNormEightVector := by
  rw [generatedFourth_local_matrix]
  unfold generatedOddAxis
  rw [generatedNormEightLine_odd_matrix, map_add, map_smul, map_smul,
    conwayMatrixAction_one, ← generatedNormEightLineMatrix_action]
  rfl

/-- Every actual diagonal coordinate has the exact integer-square formula. -/
theorem generatedEighth_matrix_diagonal_data (i : Fin 24) :
    (griessConwayEncode generatedEighthAxis).1 i i =
      1 / 4 + (generatedEighthNormEightVectorData 7 i : ℝ) ^ 2 / 32 := by
  rw [generatedEighthAxis_local_expression, generatedFourth_triality_matrix_diagonal,
    generatedEighth_middle_matrix]
  have hv : generatedNormEightVector generatedEighthNormEightVector i =
      (generatedEighthNormEightVectorData 7 i : ℝ) / Real.sqrt 8 := by
    simp only [generatedNormEightVector, generatedEighthNormEightVector_val,
      leechCoordinateEmbedding]
    rfl
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, ite_true,
    smul_eq_mul, generatedNormEightLineMatrix, Matrix.vecMulVec_apply, mul_one]
  rw [hv, ← pow_two, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  ring


/-- The original diagonal singles out its twelve medium entries and one large entry. -/
theorem generatedEighth_matrix_diagonal (i : Fin 24) :
    (griessConwayEncode generatedEighthAxis).1 i i =
      if i = 20 then (3 / 4 : ℝ) else
        if i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 6 ∨
            i = 9 ∨ i = 10 ∨ i = 16 ∨ i = 18 ∨ i = 22 ∨ i = 23 then 3 / 8 else 1 / 4 := by
  rw [generatedEighth_matrix_diagonal_data]
  fin_cases i <;> norm_num [generatedEighthNormEightVectorData]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
