/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLocalWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthSupport

/-! Transport of the finite inverse-matrix certificates to the actual local
Leech isometry and its actual preferred physical short vectors. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators

/-- The rational certificate regarded as a real matrix. -/
noncomputable def generatedFourthInverseMatrix : Matrix (Fin 24) (Fin 24) ℝ :=
  generatedFourthInverseMatrixQ.map (Rat.castHom ℝ)

/-- The displayed permutation matrix is the actual spatial source permutation. -/
theorem generatedFourth_permutation_matrix_action (v : Fin 24 → ℝ) :
    generatedFourthPermutationMatrix.map (Int.castRingHom ℝ) *ᵥ v =
      (omegaOrbitPermutationIsometry 0).val v := by
  funext i
  change _ = v ((omegaOrbitPermutation 0).symm i)
  have h (j : Fin 24) : i = omegaOrbitPermForward 0 j ↔
      j = (omegaOrbitPermutation 0).symm i := by
    change i = omegaOrbitPermutation 0 j ↔ _
    constructor
    · intro h
      simpa only [Equiv.symm_apply_apply] using
        (congrArg (omegaOrbitPermutation 0).symm h).symm
    · intro h
      rw [h, Equiv.apply_symm_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply,
    generatedFourthPermutationMatrix]
  simp_rw [h]
  simp

/-- The actual inverse local spatial map is exactly the verified rational matrix. -/
theorem generatedFourth_inverse_spatial_action (v : Fin 24 → ℝ) :
    (generatedFourthLocalFiber⁻¹).val.2.val v = generatedFourthInverseMatrix *ᵥ v := by
  have hs : (generatedFourthLocalFiber⁻¹).val.2 =
      co1XiIsometry * omegaOrbitPermutationIsometry 0 * co1XiIsometry := by
    simp only [generatedFourthLocalFiber, mul_inv_rev, inv_inv]
    rfl
  have hm : generatedFourthInverseMatrix = co1XiMatrix *
      generatedFourthPermutationMatrix.map (Int.castRingHom ℝ) * co1XiMatrix := by
    have h := congrArg (Rat.castHom ℝ).mapMatrix generatedFourth_inverse_matrix_certificate
    rw [map_mul, map_mul] at h
    exact h
  rw [hs]
  change co1XiMatrix *ᵥ ((omegaOrbitPermutationIsometry 0).val (co1XiMatrix *ᵥ v)) = _
  rw [← generatedFourth_permutation_matrix_action, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, ← hm]

/-- The normalized real coordinate vanishes exactly when its checked integer numerator does. -/
theorem generatedFourth_inverse_short_zero (r : GriessShortIndex) (i : Fin 24) :
    (generatedFourthLocalFiber⁻¹).val.2.val (griessShortVector r) i = 0 ↔
      (generatedFourthInverseNumerator *ᵥ griessShortIntegral r) i = 0 := by
  rw [generatedFourth_inverse_spatial_action]
  have hsqrt : Real.sqrt 8 ≠ 0 := by positivity
  have he : (generatedFourthInverseMatrix *ᵥ griessShortVector r) i =
      (((generatedFourthInverseNumerator *ᵥ griessShortIntegral r) i : ℤ) : ℝ) /
        (4 * Real.sqrt 8) := by
    have hm (j : Fin 24) : generatedFourthInverseMatrix i j =
        (generatedFourthInverseNumerator i j : ℝ) / 4 := by
      simp only [generatedFourthInverseMatrix, generatedFourthInverseMatrixQ, Matrix.map_apply]
      norm_num
    change (∑ j : Fin 24, generatedFourthInverseMatrix i j * griessShortVector r j) =
      ((∑ j : Fin 24, generatedFourthInverseNumerator i j * griessShortIntegral r j : ℤ) : ℝ) /
        (4 * Real.sqrt 8)
    simp_rw [hm, griessShortVector, div_mul_div_comm]
    rw [← Finset.sum_div]
    norm_cast
  rw [he, div_eq_zero_iff]
  simp [hsqrt]

/-- The finite pair-support certificate now applies to the genuine inverse Leech action. -/
theorem generatedFourth_inverse_pair_support (s : Fin 2) (p : Fin 276) :
    (∀ i : Fin 24, Nat.testBit 0xcccc00 i.val = false →
      (generatedFourthLocalFiber⁻¹).val.2.val (griessShortVector (Sum.inl (s, p))) i = 0) ↔
    s = 1 ∧ griessCoordinatePair p = (8, 11) := by
  simp_rw [generatedFourth_inverse_short_zero]
  have hlt : (griessCoordinatePair p).1 < (griessCoordinatePair p).2 :=
    (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
  have hi := generatedFourth_pair_support_certificate s
    (griessCoordinatePair p).1 (griessCoordinatePair p).2 hlt
  change (∀ i : Fin 24, Nat.testBit 0xcccc00 i.val = false →
    (generatedFourthInverseNumerator *ᵥ generatedFourthPairIntegral s
      (griessCoordinatePair p).1 (griessCoordinatePair p).2) i = 0) ↔ _
  rw [hi]
  simp only [Prod.ext_iff]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
