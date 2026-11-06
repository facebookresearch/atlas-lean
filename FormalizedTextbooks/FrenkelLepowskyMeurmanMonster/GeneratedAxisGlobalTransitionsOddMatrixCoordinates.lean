/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpatialVector

/-! Every original odd-family root matrix has a checked physical rational rank-one formula. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Complete rational matrix of the actual local odd-family root, in physical coordinates. -/
def generatedAxisGlobalOddRootMatrixQ (k : Fin 9) : Matrix (Fin 24) (Fin 24) ℚ :=
  fun i j => (if i = j then 1 / 4 else 0) +
    2 * generatedAxisGlobalOddSpatialRootVectorQ k i *
      generatedAxisGlobalOddSpatialRootVectorQ k j

private theorem oddMatrix_diagonal_rank_one :
    Matrix.diagonal generatedAxisGlobalOddMatrixDiagonal =
      (1 / 4 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) +
        (2 : ℝ) • Matrix.vecMulVec (Pi.single (0 : Fin 24) 1) (Pi.single 0 1) := by
  ext i j
  simp only [Matrix.diagonal_apply, generatedAxisGlobalOddMatrixDiagonal,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp_all

/-- Every physical matrix coefficient is the complete checked original source-word output. -/
theorem generatedAxisGlobalOddRootMatrix_actual (k : Fin 9) :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord k) generatedOddAxis)).1 =
      (generatedAxisGlobalOddRootMatrixQ k).map (Rat.castHom ℝ) := by
  rw [generatedAxisGlobalOddSourceWord_matrix, oddMatrix_diagonal_rank_one,
    map_add, map_smul, map_smul, conwayMatrixAction_one, conwayMatrixAction_vecMulVec,
    generatedAxisGlobalOddSpatialRootVector_actual]
  ext i j
  by_cases hij : i = j <;>
    simp [generatedAxisGlobalOddRootMatrixQ, Matrix.vecMulVec_apply,
      hij, mul_assoc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
