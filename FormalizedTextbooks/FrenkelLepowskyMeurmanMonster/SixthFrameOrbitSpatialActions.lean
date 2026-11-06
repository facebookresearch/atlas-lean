/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitSpatialChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitPhysicalMatrices

/-! Every literal orbit generator preserves the genuine original sixth-axis spatial matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- All cleared physical matrices are the actual fifteen source-word coordinate matrices. -/
theorem sixthFrameOrbit_original_physical_matrix (k : Fin 15) :
    leechIsomMatrix (sixthFrameOrbitOriginalIsometry k) =
      (1 / (sixthFrameOrbitSpatialDenominator k : ℝ)) •
        (sixthFrameOrbitSpatialNumerator k).map (Int.castRingHom ℝ) := by
  by_cases h : k.val < 14
  · simp only [sixthFrameOrbitOriginalIsometry, sixthFrameOrbitSpatialDenominator,
      sixthFrameOrbitSpatialNumerator, h, dite_true, ite_true, Int.cast_one, div_one, one_smul]
    exact sixthFrameOrbit_monomial_physical_matrix _
  · have hk : k = 14 := by apply Fin.ext; omega
    subst k
    change leechIsomMatrix (generatedSixthRawGenerator 4).val.2 =
      (1 / 2 : ℝ) • (sixthFrameOrbitSpatialNumerator 14).map (Int.castRingHom ℝ)
    have hc := congrArg (Int.castRingHom ℝ).mapMatrix sixthFrameOrbit_spatial_xi_product
    rw [map_mul, map_mul] at hc
    simp only [RingHom.mapMatrix_apply] at hc
    rw [sixthFrameOrbit_last_spatial, sixthFrameOrbit_isomMatrix_mul,
      sixthFrameOrbit_isomMatrix_mul, sixthFrameOrbit_monomial_physical_matrix,
      sixthFrameOrbit_xi_physical_matrix, sixthFrameOrbit_monomial_physical_matrix,
      Matrix.mul_smul, Matrix.smul_mul, hc]

/-- Actual coordinate matrices commute with the actual original sixth-axis matrix. -/
theorem sixthFrameOrbit_original_matrix_commute (k : Fin 15) :
    leechIsomMatrix (sixthFrameOrbitOriginalIsometry k) *
      (griessConwayEncode generatedSixthAxis).1 =
        (griessConwayEncode generatedSixthAxis).1 *
          leechIsomMatrix (sixthFrameOrbitOriginalIsometry k) := by
  have hc := congrArg (Int.castRingHom ℝ).mapMatrix (sixthFrameOrbit_spatial_commute k)
  rw [map_mul, map_mul] at hc
  simp only [RingHom.mapMatrix_apply] at hc
  rw [sixthFrameOrbit_original_physical_matrix, sixthFrameOrbit_axis_physical_matrix]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hc, mul_comm (1 / (sixthFrameOrbitSpatialDenominator k : ℝ)) (1 / 32)]

/-- Every original orbit isometry fixes the genuine original spatial watermark. -/
theorem sixthFrameOrbit_original_spatial_mem (k : Fin 15) :
    sixthFrameOrbitOriginalIsometry k ∈ generatedSixthSpatialStabilizer := by
  change conwayMatrixAction (sixthFrameOrbitOriginalIsometry k)
    (griessConwayEncode generatedSixthAxis).1 = (griessConwayEncode generatedSixthAxis).1
  rw [conwayMatrixAction_eq_conjugate, sixthFrameOrbit_original_matrix_commute,
    Matrix.mul_assoc,
    mul_eq_one_comm.mp (leechIsomMatrix_transpose_mul (sixthFrameOrbitOriginalIsometry k)),
    Matrix.mul_one]

/-- The exact fifteen Conway images all belong to the genuine counted spatial stabilizer. -/
theorem sixthFrameOrbit_original_co1_spatial_mem (k : Fin 15) :
    sixthFrameOrbitOriginalGenerator k ∈ generatedSixthCo1SpatialStabilizer :=
  ⟨sixthFrameOrbitOriginalIsometry k, sixthFrameOrbit_original_spatial_mem k, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
