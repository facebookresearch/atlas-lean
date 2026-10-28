/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthOddRootLabels
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthOddPhaseData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralizerGeometryShortLines

/-! Actual preferred-root and full-Q images of the 56 physical odd-root certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators
open Multiplicative

/-- The genuine inverse spatial action on any normalized integer vector. -/
theorem generatedFourth_inverse_normalized_vector (u : Fin 24 → ℤ) :
    (generatedFourthLocalFiber⁻¹).val.2.val (fun i => (u i : ℝ) / Real.sqrt 8) =
      fun i => (((generatedFourthInverseNumerator *ᵥ u) i : ℤ) : ℝ) / (4 * Real.sqrt 8) := by
  rw [generatedFourth_inverse_spatial_action]
  funext i
  change (∑ j : Fin 24, generatedFourthInverseMatrix i j * ((u j : ℝ) / Real.sqrt 8)) =
    ((∑ j : Fin 24, generatedFourthInverseNumerator i j * u j : ℤ) : ℝ) /
      (4 * Real.sqrt 8)
  simp_rw [generatedFourth_inverse_matrix_entry, div_mul_div_comm]
  rw [← Finset.sum_div]
  norm_cast

/-- Every checked integer image is the corresponding genuine physical short-vector image. -/
theorem generatedFourth_odd_inverse_vector (j : Fin 56) :
    (generatedFourthLocalFiber⁻¹).val.2.val
        (griessShortVector (generatedFourthOddRootOutputLabel j)) =
      (generatedFourthOddRootPhysicalSign j : ℝ) •
        griessShortVector (generatedFourthOddRootInputLabel j) := by
  change (generatedFourthLocalFiber⁻¹).val.2.val
    (fun i => (griessShortIntegral (generatedFourthOddRootOutputLabel j) i : ℝ) / Real.sqrt 8) = _
  rw [generatedFourth_inverse_normalized_vector]
  funext i
  rw [generatedFourth_odd_inverse_integral_certificate]
  simp only [Pi.smul_apply, smul_eq_mul, griessShortVector,
    generatedFourthOddRootInputLabel_integral, Int.cast_mul, Int.cast_ofNat]
  have hsqrt : Real.sqrt 8 ≠ 0 := by positivity
  field_simp

/-- The genuine inverse preferred-short permutation sends each odd output to its checked input. -/
theorem generatedFourth_odd_inverse_permutation (j : Fin 56) :
    griessShortPermutation (generatedFourthLocalFiber⁻¹).val.2
        (generatedFourthOddRootOutputLabel j) = generatedFourthOddRootInputLabel j := by
  have h := generatedFourth_odd_inverse_vector j
  rcases griessShortPermutation_vector (generatedFourthLocalFiber⁻¹).val.2
    (generatedFourthOddRootOutputLabel j) with hv | hv
  · exact centralizer_shortVector_line_unique _ _ _ (hv.symm.trans h)
  · apply centralizer_shortVector_line_unique _ _
      (-(generatedFourthOddRootPhysicalSign j : ℝ))
    simpa only [neg_neg, neg_smul] using congrArg Neg.neg (hv.symm.trans h)

/-- The finite phase bits are the actual preferred local-short conjugation phases. -/
theorem generatedFourth_odd_inverse_phase (j : Fin 56) :
    localShortPhase generatedFourthLocalFiber⁻¹ (generatedFourthOddRootOutputLabel j) =
      generatedFourthOddRootPhaseData j := by
  have hc := generatedFourth_odd_phase_certificate j
  rw [← generatedFourthInverseQImage_eq, monsterNortonShortQ_eq] at hc
  exact hc

/-- Every listed odd output has a genuine full preferred-Q image, including its central sign. -/
theorem generatedFourth_odd_inverse_Q_image (j : Fin 56) :
    spinConjugation (generatedFourthLocalFiber⁻¹).val.1
        (griessShortQ (generatedFourthOddRootOutputLabel j)) =
      qCentral (generatedFourthOddRootPhaseData j) *
        griessShortQ (generatedFourthOddRootInputLabel j) := by
  rw [griessShortQ_image, generatedFourth_odd_inverse_permutation,
    generatedFourth_odd_inverse_phase]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
