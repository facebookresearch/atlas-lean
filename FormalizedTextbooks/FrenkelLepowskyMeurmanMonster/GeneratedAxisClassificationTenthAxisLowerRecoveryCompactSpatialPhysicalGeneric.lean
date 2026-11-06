/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactFoundation

/-! Ungated algebraic proof drafts for genuine physical matrices and rational transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Physical coordinates preserve multiplication of the actual lattice isometries. -/
theorem generatedTenth_spatial_physical_matrix_mul (e f : leechIsomSubgroup) :
    leechIsomMatrix (e * f) = leechIsomMatrix e * leechIsomMatrix f := by
  ext j k
  change e.val (f.val (((Pi.single k (1 : ℝ)) : Fin 24 → ℝ))) j = _
  rw [← leechIsomMatrix_mulVec f, ← leechIsomMatrix_mulVec e,
    Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

/-- A genuine orthogonal inverse has the transpose physical matrix. -/
theorem generatedTenth_spatial_physical_matrix_inv (e : leechIsomSubgroup) :
    leechIsomMatrix e⁻¹ = (leechIsomMatrix e).transpose := by
  ext j k
  exact leechIsom_inverse_coordinate e k j

/-- Scalar-normalized integer matrices multiply in the actual real coordinates. -/
theorem generatedTenth_spatial_physical_scaled_mul
    (A B : Matrix (Fin 24) (Fin 24) ℤ) (a b : ℝ) :
    (a • A.map (Int.castRingHom ℝ)) * (b • B.map (Int.castRingHom ℝ)) =
      (a * b) • (A * B).map (Int.castRingHom ℝ) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.map_mul]

/-- Integer scalar certificates retain their complete real physical normalization. -/
theorem generatedTenth_spatial_physical_cast_certificate
    (U C : Matrix (Fin 24) (Fin 24) ℤ) (D K : ℕ)
    (h : D • U = K • C) :
    (D : ℝ) • U.map (Int.castRingHom ℝ) = (K : ℝ) • C.map (Int.castRingHom ℝ) := by
  ext i j
  change (D : ℝ) * (U i j : ℝ) = (K : ℝ) * (C i j : ℝ)
  have hij := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℤ => M i j) h
  simp only [Matrix.smul_apply, nsmul_eq_mul] at hij
  exact_mod_cast hij

/-- Symbolic conjugation binds every finite numerator to its genuine spatial source. -/
theorem generatedTenth_spatial_physical_conjugate
    (e f : leechIsomSubgroup) (M A C : Matrix (Fin 24) (Fin 24) ℤ)
    (r d D : ℕ) (hr : r ≠ 0) (hd : d ≠ 0)
    (he : leechIsomMatrix e = (r : ℝ)⁻¹ • M.map (Int.castRingHom ℝ))
    (hf : leechIsomMatrix f = (d : ℝ)⁻¹ • A.map (Int.castRingHom ℝ))
    (h : D • (M * A * M.transpose) = (r * r * d) • C) :
    (D : ℝ) • leechIsomMatrix (e * f * e⁻¹) = C.map (Int.castRingHom ℝ) := by
  have hm : leechIsomMatrix (e * f * e⁻¹) =
      ((r : ℝ)⁻¹ * (d : ℝ)⁻¹ * (r : ℝ)⁻¹) •
        (M * A * M.transpose).map (Int.castRingHom ℝ) := by
    rw [generatedTenth_spatial_physical_matrix_mul,
      generatedTenth_spatial_physical_matrix_mul,
      generatedTenth_spatial_physical_matrix_inv, he, hf,
      Matrix.transpose_smul, ← Matrix.transpose_map,
      generatedTenth_spatial_physical_scaled_mul,
      generatedTenth_spatial_physical_scaled_mul]
  have hc := generatedTenth_spatial_physical_cast_certificate _ _ D (r * r * d) h
  have hz : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have hw : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hs : ((r : ℝ)⁻¹ * (d : ℝ)⁻¹ * (r : ℝ)⁻¹) *
      ((r * r * d : ℕ) : ℝ) = 1 := by
    push_cast
    field_simp [hz, hw]
  rw [hm]
  calc
    _ = ((r : ℝ)⁻¹ * (d : ℝ)⁻¹ * (r : ℝ)⁻¹) •
        ((D : ℝ) • (M * A * M.transpose).map (Int.castRingHom ℝ)) := by
      rw [smul_smul, smul_smul, mul_comm (D : ℝ)]
    _ = _ := by rw [hc, smul_smul, hs, one_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
