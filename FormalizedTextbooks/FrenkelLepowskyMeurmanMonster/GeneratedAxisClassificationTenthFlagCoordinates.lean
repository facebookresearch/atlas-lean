/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthFlagData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthMatrix

/-! The entire actual tenth matrix is the flag of seven pair lines and its norm 12 line. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The real projection onto the seven original physical pair lines. -/
def generatedTenthPairProjection : Matrix (Fin 24) (Fin 24) ℝ :=
  (1 / 2 : ℝ) • generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ)

/-- The real projection onto the original signed norm 12 line. -/
def generatedTenthLineProjection : Matrix (Fin 24) (Fin 24) ℝ :=
  (1 / 6 : ℝ) • generatedTenthLineProjectionInteger.map (Int.castRingHom ℝ)

/-- Both actual real projections are idempotent and mutually orthogonal. -/
theorem generatedTenth_flag_projections :
    generatedTenthPairProjection * generatedTenthPairProjection = generatedTenthPairProjection ∧
    generatedTenthLineProjection * generatedTenthLineProjection = generatedTenthLineProjection ∧
    generatedTenthPairProjection * generatedTenthLineProjection = 0 ∧
    generatedTenthLineProjection * generatedTenthPairProjection = 0 := by
  rcases generatedTenth_integer_flag_projections with ⟨hP, hL, hPL, hLP⟩
  have hPr := congrArg (Int.castRingHom ℝ).mapMatrix hP
  have hLr := congrArg (Int.castRingHom ℝ).mapMatrix hL
  have hPLr := congrArg (Int.castRingHom ℝ).mapMatrix hPL
  have hLPr := congrArg (Int.castRingHom ℝ).mapMatrix hLP
  simp only [map_mul, map_nsmul, map_zero] at hPr hLr hPLr hLPr
  change generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) *
      generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) =
    (2 : ℕ) • generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) at hPr
  change generatedTenthLineProjectionInteger.map (Int.castRingHom ℝ) *
      generatedTenthLineProjectionInteger.map (Int.castRingHom ℝ) =
    (6 : ℕ) • generatedTenthLineProjectionInteger.map (Int.castRingHom ℝ) at hLr
  change generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) *
    generatedTenthLineProjectionInteger.map (Int.castRingHom ℝ) = 0 at hPLr
  change generatedTenthLineProjectionInteger.map (Int.castRingHom ℝ) *
    generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) = 0 at hLPr
  unfold generatedTenthPairProjection generatedTenthLineProjection
  constructor
  · rw [smul_mul_assoc, mul_smul_comm, hPr, two_nsmul, smul_add, smul_add]
    module
  constructor
  · rw [smul_mul_assoc, mul_smul_comm, hLr]
    have h6 : (6 : ℕ) • generatedTenthLineProjectionInteger.map (Int.castRingHom ℝ) =
        (6 : ℝ) • generatedTenthLineProjectionInteger.map (Int.castRingHom ℝ) := by
      ext i j
      simp [nsmul_eq_mul]
    rw [h6, smul_smul, smul_smul]
    norm_num
  constructor
  · rw [smul_mul_assoc, mul_smul_comm, hPLr, smul_zero, smul_zero]
  · rw [smul_mul_assoc, mul_smul_comm, hLPr, smul_zero, smul_zero]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Every entry is checked in the previously bound original integer matrix.
/-- The complete actual numerator is the sum of the two original integer flags. -/
theorem generatedTenth_integer_matrix_flag :
    generatedTenthMatrixNumerator = (9 : ℕ) • 1 +
      (2 : ℕ) • generatedTenthPairProjectionInteger +
      (2 : ℕ) • generatedTenthLineProjectionInteger := by
  decide +kernel

/-- The original axis matrix has exactly these genuine physical projections. -/
theorem generatedTenth_matrix_flag_actual :
    (griessConwayEncode generatedTenthAxis).1 =
      generatedTenthCoordinateFlagMatrix
        generatedTenthPairProjection generatedTenthLineProjection := by
  rw [generatedTenth_matrix_actual]
  have h := congrArg (Int.castRingHom ℝ).mapMatrix generatedTenth_integer_matrix_flag
  simp only [map_add, map_nsmul, map_one] at h
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.add_apply, Matrix.smul_apply] at hij
  simp only [generatedTenthCoordinateFlagMatrix, generatedTenthPairProjection,
    generatedTenthLineProjection, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul]
  change (generatedTenthMatrixNumerator i j : ℝ) / 32 = _
  change (generatedTenthMatrixNumerator i j : ℝ) = _ at hij
  norm_num at hij ⊢
  linarith

/-- Every actual matrix fixer preserves both original projections, with the converse. -/
theorem generatedTenth_matrix_fix_flag_iff (g : leechIsomSubgroup) :
    conwayMatrixAction g (griessConwayEncode generatedTenthAxis).1 =
      (griessConwayEncode generatedTenthAxis).1 ↔
    conwayMatrixAction g generatedTenthPairProjection = generatedTenthPairProjection ∧
      conwayMatrixAction g generatedTenthLineProjection = generatedTenthLineProjection := by
  rw [generatedTenth_matrix_flag_actual]
  rcases generatedTenth_flag_projections with ⟨hP, hL, hPL, hLP⟩
  exact generatedTenthCoordinateFlagMatrix_fix_iff g _ _ hP hL hPL hLP

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
