/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRawInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityInvariance

/-! The actual inverse octad Fourier transform, obtained from orthogonality and order three. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/-- The original octad Fourier matrix has orthonormal columns. -/
theorem generatedAxisGlobal_triality_transpose_mul :
    trialityRealMatrix.transpose * trialityRealMatrix = 1 := by
  ext i j
  have h := trialityOctadAction_pairing (Pi.single i 1 : Fin 64 → ℝ)
    (Pi.single j 1 : Fin 64 → ℝ)
  have hh : (∑ k : Fin 64, (Pi.single i 1 : Fin 64 → ℝ) k *
      (Pi.single j 1 : Fin 64 → ℝ) k) =
      if i = j then (1 : ℝ) else 0 := by
    rw [Finset.sum_eq_single i]
    · simp [Pi.single_apply]
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp
  rw [hh] at h
  simpa [trialityOctadAction_matrix, Matrix.mulVec_single, Matrix.col,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

/-- The inverse original octad Fourier matrix is its square and its transpose. -/
theorem generatedAxisGlobal_triality_square_transpose :
    trialityRealMatrix * trialityRealMatrix = trialityRealMatrix.transpose := by
  calc
    trialityRealMatrix * trialityRealMatrix =
        (trialityRealMatrix.transpose * trialityRealMatrix) *
          (trialityRealMatrix * trialityRealMatrix) := by
            rw [generatedAxisGlobal_triality_transpose_mul, one_mul]
    _ = trialityRealMatrix.transpose *
        (trialityRealMatrix * trialityRealMatrix * trialityRealMatrix) := by
          simp only [mul_assoc]
    _ = trialityRealMatrix.transpose := by rw [trialityRealMatrix_cube, mul_one]

/-- Each inverse-triality octad row is one complete original transpose Fourier sum. -/
theorem generatedAxisGlobal_inverse_octad_coordinate
    (x : GriessSpace) (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode (sExtra.symm x)).2.1 (Sum.inr (Sum.inl (o, e))) =
      ∑ f : Fin 64, trialityRealMatrix f e *
        (griessConwayEncode x).2.1 (Sum.inr (Sum.inl (o, f))) := by
  rw [generatedAxisGlobalRawInverseFormula_actual]
  change (trialityRealMatrix.mulVec
    (trialityRealMatrix.mulVec (fun f =>
      (griessConwayEncode x).2.1 (Sum.inr (Sum.inl (o, f)))))) e = _
  rw [Matrix.mulVec_mulVec, generatedAxisGlobal_triality_square_transpose]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
