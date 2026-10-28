/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthMatrixIsometryGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpatialBinaryCertificate

/-! Whole integer numerator certificates yield actual rational physical lattice isometries. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Retain the exact complete rational physical matrix. -/
def generatedTwelfthCertifiedRealMatrix (n : Matrix (Fin 24) (Fin 24) ℤ) (d : ℕ) :
    Matrix (Fin 24) (Fin 24) ℝ := (d : ℝ)⁻¹ • n.map (Int.castRingHom ℝ)

/-- Whole integer orthogonality transfers to the actual real rational matrix. -/
theorem generatedTwelfth_certified_real_left (n : Matrix (Fin 24) (Fin 24) ℤ)
    (d : ℕ) (hd : d ≠ 0) (h : n.transpose * n = (d * d : ℤ) • 1) :
    (generatedTwelfthCertifiedRealMatrix n d).transpose *
      generatedTwelfthCertifiedRealMatrix n d = 1 := by
  have hr := congrArg (Int.castRingHom ℝ).mapMatrix h
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map] at hr
  have hn : (n.map (Int.castRingHom ℝ)).transpose * n.map (Int.castRingHom ℝ) =
      ((d : ℝ) * (d : ℝ)) • (1 : Matrix (Fin 24) (Fin 24) ℝ) := by
    rw [hr]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply]
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, Matrix.one_apply]
    split_ifs <;> norm_num
  rw [generatedTwelfthCertifiedRealMatrix, Matrix.transpose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hn, smul_smul]
  have hz : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have he : (d : ℝ)⁻¹ * (d : ℝ)⁻¹ * ((d : ℝ) * (d : ℝ)) = 1 := by
    field_simp [hz]
  rw [he, one_smul]

/-- The other full orientation follows from its exact integer orthogonality certificate. -/
theorem generatedTwelfth_certified_real_right (n : Matrix (Fin 24) (Fin 24) ℤ)
    (d : ℕ) (hd : d ≠ 0) (h : n * n.transpose = (d * d : ℤ) • 1) :
    generatedTwelfthCertifiedRealMatrix n d *
      (generatedTwelfthCertifiedRealMatrix n d).transpose = 1 := by
  have hl := generatedTwelfth_certified_real_left n.transpose d hd (by simpa using h)
  simpa [generatedTwelfthCertifiedRealMatrix, Matrix.transpose_smul,
    Matrix.transpose_map] using hl

/-- The full integer basis certificate binds every actual real lattice column. -/
theorem generatedTwelfth_certified_real_basis (n c : Matrix (Fin 24) (Fin 24) ℤ)
    (d : ℕ) (hd : d ≠ 0) (h : n * leechBasisMatrix =
      (d : ℤ) • (leechBasisMatrix * c)) :
    generatedTwelfthCertifiedRealMatrix n d * leechBasisMatrix.map (Int.castRingHom ℝ) =
      leechBasisMatrix.map (Int.castRingHom ℝ) * c.map (Int.castRingHom ℝ) := by
  have hr := congrArg (Int.castRingHom ℝ).mapMatrix h
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul] at hr
  have hn : n.map (Int.castRingHom ℝ) * leechBasisMatrix.map (Int.castRingHom ℝ) =
      (d : ℝ) • (leechBasisMatrix.map (Int.castRingHom ℝ) *
        c.map (Int.castRingHom ℝ)) := by
    rw [hr]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply]
    simp only [zsmul_eq_mul, ← Matrix.map_mul, Matrix.map_apply]
    simp [smul_eq_mul]
  rw [generatedTwelfthCertifiedRealMatrix, Matrix.smul_mul, hn, smul_smul]
  have hz : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  rw [inv_mul_cancel₀ hz, one_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
