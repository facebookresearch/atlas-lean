/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact physical inverse matrix of the actual Norton Leech component. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderMatrix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The exact rational inverse physical matrix from the proved twelfth Norton numerator. -/
def monsterNortonUInversePhysicalMatrixQ : Matrix (Fin 24) (Fin 24) ℚ :=
  (1 / 4 : ℚ) • monsterNortonUNumerator12.map (Int.castRingHom ℚ)

/-- This physical matrix is a genuine left inverse of the actual source-word matrix. -/
theorem monsterNortonUInversePhysicalMatrixQ_mul :
    monsterNortonUInversePhysicalMatrixQ * monsterNortonUMatrixQ = 1 := by
  rw [monsterNortonUInversePhysicalMatrixQ, ← monsterNortonUMatrixQ_twelve,
    ← pow_succ, monsterNortonUMatrixQ_thirteen]

private theorem inverse_apply_cancel (S : Subgroup ((Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ)))
    (e : S) (x : Fin 24 → ℝ) : e.val ((e⁻¹).val x) = x :=
  LinearEquiv.apply_symm_apply e.val x

/-- The actual inverse Norton lattice action is exactly the rational inverse physical matrix. -/
theorem monsterNortonUInversePhysicalMatrix_actual (x : Fin 24 → ℝ) :
    (monsterNortonUFiber.val.2⁻¹).val x =
      monsterNortonUInversePhysicalMatrixQ.map (Rat.castHom ℝ) *ᵥ x := by
  have hm := congrArg (Rat.castHom ℝ).mapMatrix monsterNortonUInversePhysicalMatrixQ_mul
  rw [map_mul, map_one] at hm
  simp only [RingHom.mapMatrix_apply] at hm
  have h := congrArg (monsterNortonUInversePhysicalMatrixQ.map (Rat.castHom ℝ)).mulVec
    (inverse_apply_cancel _ monsterNortonUFiber.val.2 x)
  rw [monsterNortonUFiber_leech_matrix, Matrix.mulVec_mulVec, hm, Matrix.one_mulVec] at h
  exact h

/-- Every inverse physical basis column has its exact original denominator four. -/
theorem monsterNortonUInversePhysicalMatrix_basis (k i : Fin 24) :
    (monsterNortonUFiber.val.2⁻¹).val (Pi.single k 1) i =
      (1 / 4 : ℝ) * (monsterNortonUNumerator12 i k : ℝ) := by
  rw [monsterNortonUInversePhysicalMatrix_actual]
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, monsterNortonUInversePhysicalMatrixQ,
    Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  change (((1 / 4 : ℚ) * (monsterNortonUNumerator12 i k : ℚ) : ℚ) : ℝ) = _
  push_cast
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
