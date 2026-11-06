/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthPairSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates

/-! Exact original matrix watermark of the literal fifth transition candidate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original diagonal entry comes from the finite inverse spatial certificate. -/
theorem generatedFifth_matrix_diagonal (i : Fin 24) :
    (griessConwayEncode generatedFifthAxis).1 i i =
      (generatedFifthProjectionDiagonal i : ℝ) / 16 := by
  rw [generatedFifthAxis_local_expression, generatedFourth_triality_matrix_diagonal,
    generatedFourth_local_matrix, generatedAxis_triality_octad_matrix,
    generatedFourthOctad_mask]
  exact generatedFifth_projection_diagonal i

/-- Every original off-diagonal entry is zero because all actual middle pair rows vanish. -/
theorem generatedFifth_matrix_off_diagonal (i j : Fin 24) (hij : i ≠ j) :
    (griessConwayEncode generatedFifthAxis).1 i j = 0 := by
  rw [generatedFifthAxis_local_expression,
    generatedFourth_triality_matrix_off_diagonal _ i j hij, generatedFourth_local_short,
    generatedFifth_middle_pair_zero, generatedFifth_middle_pair_zero]
  norm_num

/-- The original watermark is one quarter identity plus one quarter actual octad projection. -/
theorem generatedFifth_matrix :
    (griessConwayEncode generatedFifthAxis).1 = Matrix.diagonal (fun i : Fin 24 =>
      if Nat.testBit 0x0f000f i.val then (1 / 2 : ℝ) else 1 / 4) := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, generatedFifth_matrix_diagonal]
    have h : ∀ i : Fin 24, generatedFifthProjectionDiagonal i =
        if Nat.testBit 0x0f000f i.val then 8 else 4 := by decide +kernel
    rw [h]
    split_ifs <;> norm_num
  · rw [Matrix.diagonal_apply_ne _ hij, generatedFifth_matrix_off_diagonal i j hij]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
