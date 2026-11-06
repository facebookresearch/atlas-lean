/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftAxisFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXi

/-! A genuine nontrivial Golay-sign lift obtained by cubing the full fourth-axis lift. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The exact rational physical matrix of the normalized signed flag generator. -/
def generatedFourthFlagMatrixQ : Matrix (Fin 24) (Fin 24) ℚ := fun i j =>
  (if monsterSourceY82SignCode.val i = 0 then 1 else -1) *
    co1XiMatrixQ (generatedFourthFlagCorrectionCoordinates i) j *
      (if monsterSourceY82SignCode.val j = 0 then 1 else -1)

/-- The physical cube fixes the first eight coordinates and negates the remaining sixteen. -/
def generatedFourthFlagCubeMatrixQ : Matrix (Fin 24) (Fin 24) ℚ :=
  Matrix.diagonal (fun i => if i.val < 8 then 1 else -1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
-- Check all 576 rational matrix entries of the literal signed cube.
/-- Exact rational arithmetic verifies the signed physical cube, including its orientation. -/
theorem generatedFourth_flag_matrix_cube_certificate :
    generatedFourthFlagMatrixQ * generatedFourthFlagMatrixQ * generatedFourthFlagMatrixQ =
      generatedFourthFlagCubeMatrixQ := by
  decide +kernel

/-- The genuine normalized isometry acts by the checked exact rational physical matrix. -/
theorem generatedFourth_flag_matrix_apply (x : Fin 24 → ℝ) :
    generatedFourthFlagNormalizedLift.val.2.val x =
      (generatedFourthFlagMatrixQ.map (Rat.castHom ℝ)) *ᵥ x := by
  rw [show generatedFourthFlagNormalizedLift.val.2 =
    golaySignIsometry monsterSourceY82SignCode * generatedFourthFlagCorrectionLeech *
      co1XiIsometry * golaySignIsometry monsterSourceY82SignCode from rfl]
  funext i
  change qSign (monsterSourceY82SignCode.val i) *
    (co1XiMatrix *ᵥ golayRealSign monsterSourceY82SignCode.val x)
      (generatedFourthFlagCorrectionCoordinates i) = _
  simp only [Matrix.mulVec, dotProduct, generatedFourthFlagMatrixQ, Matrix.map_apply,
    co1XiMatrix, co1XiMatrixQ, apply_ite,
    golayRealSign_apply, qSign]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [map_mul, map_neg, map_one] <;> ring

/-- Cubing the genuine spatial isometry gives the literal sixteen-coordinate sign change. -/
theorem generatedFourth_flag_cube_apply (x : Fin 24 → ℝ) :
    (generatedFourthFlagNormalizedLift.val.2 ^ 3).val x =
      fun i => if i.val < 8 then x i else -x i := by
  change generatedFourthFlagNormalizedLift.val.2.val
    (generatedFourthFlagNormalizedLift.val.2.val
      (generatedFourthFlagNormalizedLift.val.2.val x)) = _
  rw [generatedFourth_flag_matrix_apply, generatedFourth_flag_matrix_apply,
    generatedFourth_flag_matrix_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h := congrArg (fun A : Matrix (Fin 24) (Fin 24) ℚ => A.map (Rat.castHom ℝ))
    generatedFourth_flag_matrix_cube_certificate
  simp only [Matrix.map_mul] at h
  rw [h]
  funext i
  simp only [generatedFourthFlagCubeMatrixQ, Matrix.diagonal_map (map_zero _),
    Matrix.mulVec_diagonal]
  by_cases hi : i.val < 8 <;> simp [hi]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
