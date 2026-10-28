/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7ConjugationVectors

/-! The actual real lattice isometry intertwines the complete seven-pair and octad projectors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The certified original isometry intertwines the complete actual real projectors. -/
theorem generatedTenth_e7_pair_projection_real :
    generatedTenthE7Matrix * generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) *
      generatedTenthE7Matrix.transpose =
        generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) := by
  have h := congrArg (Int.castRingHom ℝ).mapMatrix
    generatedTenth_e7_pair_projection_integer
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map] at h
  have hs : ((4 : ℤ) • generatedTenthE7ProjectionInteger).map (Int.castRingHom ℝ) =
      (4 : ℝ) • generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply]
    simp only [smul_eq_mul, map_mul, map_ofNat]
  rw [hs] at h
  simp only [generatedTenthE7Matrix, generatedTwelfthCertifiedRealMatrix,
    Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h, smul_smul]
  norm_num

/-- Every real vector is transported with its full original projector action retained. -/
theorem generatedTenth_e7_pair_projection_intertwine :
    generatedTenthE7Matrix * generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) =
      generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) * generatedTenthE7Matrix := by
  have hi : generatedTenthE7Matrix.transpose * generatedTenthE7Matrix = 1 :=
    generatedTwelfth_certified_real_left _ 2 (by decide)
      generatedTenth_e7_conjugation_orthogonal_left
  calc
    _ = (generatedTenthE7Matrix *
        generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ)) *
          (generatedTenthE7Matrix.transpose * generatedTenthE7Matrix) := by rw [hi, mul_one]
    _ = (generatedTenthE7Matrix *
        generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) *
          generatedTenthE7Matrix.transpose) * generatedTenthE7Matrix := by
      simp only [mul_assoc]
    _ = _ := by rw [generatedTenth_e7_pair_projection_real]

/-- The complete actual eigenspace, in both directions, is the transported octad hyperplane. -/
theorem generatedTenth_e7_pair_eigenspace_iff (x : Fin 24 → ℝ) :
    generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) *ᵥ x = (2 : ℝ) • x ↔
      generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ
          (generatedTenthE7Matrix *ᵥ x) = (2 : ℝ) • (generatedTenthE7Matrix *ᵥ x) := by
  constructor
  · intro h
    rw [Matrix.mulVec_mulVec, ← generatedTenth_e7_pair_projection_intertwine,
      ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul]
  · intro h
    apply generatedTenthE7Isometry.val.injective
    change generatedTenthE7Matrix *ᵥ
        (generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) *ᵥ x) =
      generatedTenthE7Matrix *ᵥ ((2 : ℝ) • x)
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      generatedTenth_e7_pair_projection_intertwine, ← Matrix.mulVec_mulVec]
    exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
