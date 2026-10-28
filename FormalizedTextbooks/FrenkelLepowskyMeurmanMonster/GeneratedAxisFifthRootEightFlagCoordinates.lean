/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightFlagData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightFlagMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightMatrix

/-! Bind both distinguished line projections to the entire original root-8 axis matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The orthogonal projection onto the original higher distinguished line. -/
def generatedFifthRootEightHighProjection : Matrix (Fin 24) (Fin 24) ℝ :=
  (1 / 10 : ℝ) • generatedFifthRootEightHighProjectionInteger.map (Int.castRingHom ℝ)

/-- The orthogonal projection onto the original lower distinguished line. -/
def generatedFifthRootEightLowProjection : Matrix (Fin 24) (Fin 24) ℝ :=
  (1 / 2 : ℝ) • generatedFifthRootEightLowProjectionInteger.map (Int.castRingHom ℝ)

/-- The actual projections are idempotent and mutually orthogonal. -/
theorem generatedFifthRootEight_flag_projections :
    generatedFifthRootEightHighProjection * generatedFifthRootEightHighProjection =
        generatedFifthRootEightHighProjection ∧
    generatedFifthRootEightLowProjection * generatedFifthRootEightLowProjection =
        generatedFifthRootEightLowProjection ∧
    generatedFifthRootEightHighProjection * generatedFifthRootEightLowProjection = 0 ∧
    generatedFifthRootEightLowProjection * generatedFifthRootEightHighProjection = 0 := by
  rcases generatedFifthRootEight_integer_flag_projections with ⟨hP, hL, hPL, hLP⟩
  have hPr := congrArg (Int.castRingHom ℝ).mapMatrix hP
  have hLr := congrArg (Int.castRingHom ℝ).mapMatrix hL
  have hPLr := congrArg (Int.castRingHom ℝ).mapMatrix hPL
  have hLPr := congrArg (Int.castRingHom ℝ).mapMatrix hLP
  simp only [map_mul, map_nsmul, map_zero] at hPr hLr hPLr hLPr
  have hn (n : ℕ) (A : Matrix (Fin 24) (Fin 24) ℝ) : n • A = (n : ℝ) • A := by
    ext i j
    simp [nsmul_eq_mul]
  simp_rw [hn] at hPr hLr
  change generatedFifthRootEightHighProjectionInteger.map (Int.castRingHom ℝ) *
      generatedFifthRootEightHighProjectionInteger.map (Int.castRingHom ℝ) =
    (10 : ℝ) • generatedFifthRootEightHighProjectionInteger.map (Int.castRingHom ℝ) at hPr
  change generatedFifthRootEightLowProjectionInteger.map (Int.castRingHom ℝ) *
      generatedFifthRootEightLowProjectionInteger.map (Int.castRingHom ℝ) =
    (2 : ℝ) • generatedFifthRootEightLowProjectionInteger.map (Int.castRingHom ℝ) at hLr
  change generatedFifthRootEightHighProjectionInteger.map (Int.castRingHom ℝ) *
    generatedFifthRootEightLowProjectionInteger.map (Int.castRingHom ℝ) = 0 at hPLr
  change generatedFifthRootEightLowProjectionInteger.map (Int.castRingHom ℝ) *
    generatedFifthRootEightHighProjectionInteger.map (Int.castRingHom ℝ) = 0 at hLPr
  unfold generatedFifthRootEightHighProjection generatedFifthRootEightLowProjection
  constructor
  · rw [smul_mul_assoc, mul_smul_comm, hPr, smul_smul, smul_smul]
    norm_num
  constructor
  · rw [smul_mul_assoc, mul_smul_comm, hLr, smul_smul, smul_smul]
    norm_num
  constructor
  · rw [smul_mul_assoc, mul_smul_comm, hPLr, smul_zero, smul_zero]
  · rw [smul_mul_assoc, mul_smul_comm, hLPr, smul_zero, smul_zero]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check every original integer entry against the two distinguished rank-one flags.
/-- The entire certified numerator is the original scalar matrix plus its two flags. -/
theorem generatedFifthRootEight_integer_matrix_flag :
    generatedFifthRootEightMatrixNumerator = (5 : ℕ) • 1 +
      generatedFifthRootEightHighProjectionInteger -
      generatedFifthRootEightLowProjectionInteger := by
  decide +kernel

/-- The complete actual root-8 matrix is precisely its two distinguished line projections. -/
theorem generatedFifthRootEight_matrix_flag_actual :
    (griessConwayEncode generatedFifthRootEightAxis).1 =
      generatedFifthRootEightCoordinateFlagMatrix
        generatedFifthRootEightHighProjection generatedFifthRootEightLowProjection := by
  rw [generatedFifthRootEight_matrix_actual]
  have h := congrArg (Int.castRingHom ℝ).mapMatrix generatedFifthRootEight_integer_matrix_flag
  simp only [map_sub, map_add, map_nsmul, map_one] at h
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply] at hij
  simp only [generatedFifthRootEightCoordinateFlagMatrix, generatedFifthRootEightHighProjection,
    generatedFifthRootEightLowProjection, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  change (generatedFifthRootEightMatrixNumerator i j : ℝ) / 16 = _
  change (generatedFifthRootEightMatrixNumerator i j : ℝ) = _ at hij
  norm_num at hij ⊢
  linarith

/-- Fixing the actual matrix is equivalent to preserving both original distinguished lines. -/
theorem generatedFifthRootEight_matrix_fix_flag_iff (g : leechIsomSubgroup) :
    conwayMatrixAction g (griessConwayEncode generatedFifthRootEightAxis).1 =
      (griessConwayEncode generatedFifthRootEightAxis).1 ↔
    conwayMatrixAction g generatedFifthRootEightHighProjection =
        generatedFifthRootEightHighProjection ∧
      conwayMatrixAction g generatedFifthRootEightLowProjection =
        generatedFifthRootEightLowProjection := by
  rw [generatedFifthRootEight_matrix_flag_actual]
  rcases generatedFifthRootEight_flag_projections with ⟨hP, hL, hPL, hLP⟩
  exact generatedFifthRootEightCoordinateFlagMatrix_fix_iff g _ _ hP hL hPL hLP

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
