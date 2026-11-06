/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinMatrixCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompatibility
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

/-! Complete actual matrix fixation requires only the genuine source spatial cache equality. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Rational spatial source binding turns all integer covariance packets into actual matrix
fixation. -/
theorem generatedNinth_lower_spin_direct_matrix_fix_of_source_cache (i : Fin 11)
    (hspatial : ∀ j k, (generatedNinthLowerSpinTensorSpatialDenominator i : ℝ) *
      (generatedNinthLowerSpinDirectIsometry i).val (Pi.single k 1) j =
        (generatedNinthLowerSpinTensorSpatialNumerator i j k : ℝ)) :
    localMatrixRepresentation (generatedNinthLowerSpinDirectFiber i)
      (griessConwayEncode generatedNinthAxis).1 = (griessConwayEncode generatedNinthAxis).1 := by
  let d : ℝ := generatedNinthLowerSpinTensorSpatialDenominator i
  let A := leechIsomMatrix (generatedNinthLowerSpinDirectIsometry i)
  let N : Matrix (Fin 24) (Fin 24) ℝ := fun j k => (generatedNinthMatrixNumerator j k : ℝ)
  let P : Matrix (Fin 24) (Fin 24) ℝ :=
    fun j k => (generatedNinthLowerSpinTensorSpatialNumerator i j k : ℝ)
  have hd : d ≠ 0 := by
    have hp : ∀ l : Fin 11, 0 < generatedNinthLowerSpinTensorSpatialDenominator l := by
      decide +kernel
    dsimp [d]
    exact_mod_cast (ne_of_gt (hp i))
  have hP : d • A = P := by
    ext j k
    exact hspatial j k
  have hcov : P * N * P.transpose = d ^ 2 • N := by
    ext j k
    have h := generatedNinth_lower_spin_matrix_certificates i j k
    unfold generatedNinthLowerSpinMatrixCondition generatedNinthLowerSpinMatrixNumerator at h
    have hc := congrArg (fun z : ℤ => (z : ℝ)) h
    simpa only [P, N, d, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.smul_apply,
      smul_eq_mul, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast] using hc
  rw [← hP] at hcov
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at hcov
  have hfixed : A * N * A.transpose = N := by
    ext j k
    have hc := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℝ => M j k) hcov
    simp only [Matrix.smul_apply, smul_eq_mul, ← pow_two] at hc
    exact mul_left_cancel₀ (pow_ne_zero 2 hd) hc
  have hN : generatedNinthAxisMatrix = (1 / 32 : ℝ) • N := by
    ext j k
    simp only [generatedNinthAxisMatrix, N, Matrix.smul_apply, smul_eq_mul]
    ring
  change conwayMatrixAction (generatedNinthLowerSpinDirectIsometry i)
    (griessConwayEncode generatedNinthAxis).1 = (griessConwayEncode generatedNinthAxis).1
  rw [generatedNinth_axis_matrix, hN, map_smul, conwayMatrixAction_eq_conjugate, hfixed]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
