/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthSupport

/-! Exact transport of the fifth candidate's finite inverse matrix to its actual local action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators

/-- The original rational inverse certificate viewed over the real physical space. -/
def generatedFifthInverseMatrix : Matrix (Fin 24) (Fin 24) ℝ :=
  generatedFifthInverseMatrixQ.map (Rat.castHom ℝ)

/-- Each literal physical permutation matrix acts by the actual frozen source permutation. -/
theorem generatedFifth_permutation_matrix_action (k : Fin 2) (v : Fin 24 → ℝ) :
    (generatedFifthPermutationMatrix k).map (Int.castRingHom ℝ) *ᵥ v =
      (omegaOrbitPermutationIsometry k).val v := by
  funext i
  change _ = v ((omegaOrbitPermutation k).symm i)
  have h (j : Fin 24) : i = omegaOrbitPermForward k j ↔
      j = (omegaOrbitPermutation k).symm i := by
    change i = omegaOrbitPermutation k j ↔ _
    constructor
    · intro h
      simpa only [Equiv.symm_apply_apply] using
        (congrArg (omegaOrbitPermutation k).symm h).symm
    · intro h
      rw [h, Equiv.apply_symm_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, generatedFifthPermutationMatrix]
  simp_rw [h]
  simp

/-- The literal Xi*P1*P0*Xi is exactly the actual inverse spatial action. -/
theorem generatedFifth_inverse_spatial_action (v : Fin 24 → ℝ) :
    (generatedFifthLocalFiber⁻¹).val.2.val v = generatedFifthInverseMatrix *ᵥ v := by
  have hs : (generatedFifthLocalFiber⁻¹).val.2 = co1XiIsometry *
      omegaOrbitPermutationIsometry 1 * omegaOrbitPermutationIsometry 0 * co1XiIsometry := by
    simp only [generatedFifthLocalFiber, mul_inv_rev, inv_inv]
    rfl
  have hm : generatedFifthInverseMatrix = co1XiMatrix *
      (generatedFifthPermutationMatrix 1).map (Int.castRingHom ℝ) *
      (generatedFifthPermutationMatrix 0).map (Int.castRingHom ℝ) * co1XiMatrix := by
    have h := congrArg (Rat.castHom ℝ).mapMatrix generatedFifth_inverse_matrix_certificate
    rw [map_mul, map_mul, map_mul] at h
    exact h
  rw [hs]
  change co1XiMatrix *ᵥ ((omegaOrbitPermutationIsometry 1).val
    ((omegaOrbitPermutationIsometry 0).val (co1XiMatrix *ᵥ v))) = _
  rw [← generatedFifth_permutation_matrix_action, ← generatedFifth_permutation_matrix_action,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hm]

/-- The normalized real coordinate vanishes exactly when its checked integer numerator does. -/
theorem generatedFifth_inverse_short_zero (r : GriessShortIndex) (i : Fin 24) :
    (generatedFifthLocalFiber⁻¹).val.2.val (griessShortVector r) i = 0 ↔
      (generatedFifthInverseNumerator *ᵥ griessShortIntegral r) i = 0 := by
  rw [generatedFifth_inverse_spatial_action]
  have hsqrt : Real.sqrt 8 ≠ 0 := by positivity
  have he : (generatedFifthInverseMatrix *ᵥ griessShortVector r) i =
      (((generatedFifthInverseNumerator *ᵥ griessShortIntegral r) i : ℤ) : ℝ) /
        (4 * Real.sqrt 8) := by
    have hm (j : Fin 24) : generatedFifthInverseMatrix i j =
        (generatedFifthInverseNumerator i j : ℝ) / 4 := by
      simp only [generatedFifthInverseMatrix, generatedFifthInverseMatrixQ, Matrix.map_apply]
      norm_num
    change (∑ j : Fin 24, generatedFifthInverseMatrix i j * griessShortVector r j) =
      ((∑ j : Fin 24, generatedFifthInverseNumerator i j * griessShortIntegral r j : ℤ) : ℝ) /
        (4 * Real.sqrt 8)
    simp_rw [hm, griessShortVector, div_mul_div_comm]
    rw [← Finset.sum_div]
    norm_cast
  rw [he, div_eq_zero_iff]
  simp [hsqrt]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
