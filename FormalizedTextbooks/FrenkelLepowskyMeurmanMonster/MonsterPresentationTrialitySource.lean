/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Triality orientation in the actual dictionary representation.
Seysen §8.1, (8.1.4): source right-row tau = y_tau x_tau has octad coefficient
H(delta,epsilon) sign(epsilon)/8. The actual sExtra is its transpose.
Thus the inverse-transpose convention for literal source words uses sExtra inverse.
The public mmgroup mm_group.py documentation identifies tag t with this Seysen tau.
This proves coordinate formulas, not the missing presentation kernel or recognition.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityBasisVectors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalSubgroups

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The primary source right-row coefficients of tau on an octad block. -/
noncomputable def monsterSourceTrialityOctadRows : Matrix (Fin 64) (Fin 64) ℝ :=
  fun δ ε => (1 / 8 : ℝ) * (trialityHadamard δ ε : ℝ) *
    (trialityIntegerDiagonal ε : ℝ)

/-- The actual octad matrix is exactly the transpose of the source right-row matrix. -/
theorem monsterSourceTrialityOctadRows_transpose :
    monsterSourceTrialityOctadRows.transpose = trialityRealMatrix := by
  ext i j
  change (1 / 8 : ℝ) * (trialityHadamard j i : ℝ) *
    (trialityIntegerDiagonal i : ℝ) =
      (1 / 8 : ℝ) * ((trialityIntegerDiagonal i * trialityHadamard i j : ℤ) : ℝ)
  rw [Int.cast_mul]
  rw [trialityHadamard_symmetric j i]
  ring

/-- Every actual octad basis coefficient agrees with the primary right-row source formula. -/
theorem monsterSourceTriality_octad_basis (δ ε : Fin 64) :
    trialityOctadAction (Pi.single δ 1) ε = monsterSourceTrialityOctadRows δ ε := by
  rw [trialityOctadAction_matrix, Matrix.mulVec_single_one,
    ← monsterSourceTrialityOctadRows_transpose]
  rfl

/-- The actual normalized matrix squares to its transpose. -/
theorem monsterSourceTrialityRealMatrix_square :
    trialityRealMatrix * trialityRealMatrix = trialityRealMatrix.transpose := by
  have hm : trialityIntegerMatrix.map (Int.castRingHom ℝ) *
      trialityIntegerMatrix.map (Int.castRingHom ℝ) =
      (8 : ℝ) • trialityIntegerMatrix.transpose.map (Int.castRingHom ℝ) := by
    change (Int.castRingHom ℝ).mapMatrix trialityIntegerMatrix *
      (Int.castRingHom ℝ).mapMatrix trialityIntegerMatrix = _
    rw [← map_mul, trialityIntegerMatrix_square]
    ext i j
    change (((8 : ℤ) * trialityIntegerMatrix.transpose i j : ℤ) : ℝ) =
      (8 : ℝ) * (trialityIntegerMatrix.transpose i j : ℝ)
    rw [Int.cast_mul, Int.cast_ofNat]
  simp only [trialityRealMatrix, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hm, smul_smul]
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  ring

/-- The actual inverse octad operation applies the source right-row matrix to columns. -/
theorem monsterSourceTriality_octad_inverse (f : Fin 64 → ℝ) :
    trialityOctadAction.symm f = monsterSourceTrialityOctadRows.mulVec f := by
  have hi : trialityOctadAction.symm f = trialityOctadAction (trialityOctadAction f) := by
    apply trialityOctadAction.injective
    rw [LinearEquiv.apply_symm_apply, trialityOctadAction_triple]
  rw [hi, trialityOctadAction_matrix, trialityOctadAction_matrix,
    Matrix.mulVec_mulVec, monsterSourceTrialityRealMatrix_square,
    ← monsterSourceTrialityOctadRows_transpose, Matrix.transpose_transpose]

/-- The actual element selected by the inverse-transpose source convention for tag t1. -/
noncomputable def monsterSourceTriality : ↥G := extraIntoGenerated⁻¹

/-- This actual source assignment obeys the order-three relation. -/
theorem monsterSourceTriality_cube : monsterSourceTriality ^ 3 = 1 := by
  apply Subtype.ext
  change (sExtra⁻¹) ^ 3 = 1
  rw [inv_pow, sExtra_pow_three, inv_one]

/-- Inverse transpose reverses the primary X,Y,Z basis cycle. -/
theorem monsterSourceTriality_XYZ_basis (s : Fin 3) (k : Fin 49152) :
    (monsterSourceTriality : GriessSpace ≃ₗ[ℝ] GriessSpace) (trialityXYZBasis s k) =
      trialityXYZBasis (trialityCycle.symm s) k := by
  change sExtra.symm (trialityXYZBasis s k) = _
  apply sExtra.injective
  rw [LinearEquiv.apply_symm_apply, sExtra_XYZ_basis, Equiv.apply_symm_apply]

/-- The same inverse-transpose convention reverses the primary A,B,C basis cycle. -/
theorem monsterSourceTriality_ABC_basis (s : Fin 3) (p : Fin 276) :
    (monsterSourceTriality : GriessSpace ≃ₗ[ℝ] GriessSpace) (trialityABCBasis s p) =
      trialityABCBasis (trialityCycle.symm s) p := by
  change sExtra.symm (trialityABCBasis s p) = _
  apply sExtra.injective
  rw [LinearEquiv.apply_symm_apply, sExtra_ABC_basis, Equiv.apply_symm_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
