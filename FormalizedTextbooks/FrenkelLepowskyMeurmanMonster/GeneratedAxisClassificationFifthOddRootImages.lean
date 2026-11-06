/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthOddRootLabels
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthOddRootPhysical
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthOddPhaseData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralizerGeometryShortLines

/-! Actual preferred-root and full-Q images of the 64 physical odd-root certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators
open Multiplicative

/-- The genuine inverse spatial action on any normalized integer vector. -/
theorem generatedFifth_inverse_normalized_vector (u : Fin 24 → ℤ) :
    (generatedFifthLocalFiber⁻¹).val.2.val (fun i => (u i : ℝ) / Real.sqrt 8) =
      fun i => (((generatedFifthInverseNumerator *ᵥ u) i : ℤ) : ℝ) / (4 * Real.sqrt 8) := by
  rw [generatedFifth_inverse_spatial_action]
  funext i
  change (∑ j : Fin 24, generatedFifthInverseMatrix i j * ((u j : ℝ) / Real.sqrt 8)) =
    ((∑ j : Fin 24, generatedFifthInverseNumerator i j * u j : ℤ) : ℝ) /
      (4 * Real.sqrt 8)
  simp_rw [generatedFifth_inverse_matrix_entry, div_mul_div_comm]
  rw [← Finset.sum_div]
  norm_cast

/-- Every checked integer image is the corresponding genuine physical short-vector image. -/
theorem generatedFifth_odd_inverse_vector (j : Fin 64) :
    (generatedFifthLocalFiber⁻¹).val.2.val
        (griessShortVector (generatedFifthOddRootOutputLabel j)) =
      (generatedFifthOddRootPhysicalSign j : ℝ) •
        griessShortVector (generatedFifthOddRootInputLabel j) := by
  change (generatedFifthLocalFiber⁻¹).val.2.val
    (fun i => (griessShortIntegral (generatedFifthOddRootOutputLabel j) i : ℝ) / Real.sqrt 8) = _
  rw [generatedFifth_inverse_normalized_vector]
  funext i
  rw [generatedFifth_odd_inverse_integral_certificate]
  simp only [Pi.smul_apply, smul_eq_mul, griessShortVector,
    generatedFifthOddRootInputLabel_integral, Int.cast_mul, Int.cast_ofNat]
  have hsqrt : Real.sqrt 8 ≠ 0 := by positivity
  field_simp

/-- The genuine inverse preferred-short permutation sends each odd output to its checked input. -/
theorem generatedFifth_odd_inverse_permutation (j : Fin 64) :
    griessShortPermutation (generatedFifthLocalFiber⁻¹).val.2
        (generatedFifthOddRootOutputLabel j) = generatedFifthOddRootInputLabel j := by
  have h := generatedFifth_odd_inverse_vector j
  rcases griessShortPermutation_vector (generatedFifthLocalFiber⁻¹).val.2
    (generatedFifthOddRootOutputLabel j) with hv | hv
  · exact centralizer_shortVector_line_unique _ _ _ (hv.symm.trans h)
  · apply centralizer_shortVector_line_unique _ _
      (-(generatedFifthOddRootPhysicalSign j : ℝ))
    simpa only [neg_neg, neg_smul] using congrArg Neg.neg (hv.symm.trans h)

/-- The finite phase bits are the actual preferred local-short conjugation phases. -/
theorem generatedFifth_odd_inverse_phase (j : Fin 64) :
    localShortPhase generatedFifthLocalFiber⁻¹ (generatedFifthOddRootOutputLabel j) =
      generatedFifthOddRootPhaseData j := by
  have hc := generatedFifth_odd_phase_certificate j
  rw [← generatedFifthInverseQImage_eq, monsterNortonShortQ_eq] at hc
  exact hc

/-- Every listed odd output has a genuine full preferred-Q image, including its central sign. -/
theorem generatedFifth_odd_inverse_Q_image (j : Fin 64) :
    spinConjugation (generatedFifthLocalFiber⁻¹).val.1
        (griessShortQ (generatedFifthOddRootOutputLabel j)) =
      qCentral (generatedFifthOddRootPhaseData j) *
        griessShortQ (generatedFifthOddRootInputLabel j) := by
  rw [griessShortQ_image, generatedFifth_odd_inverse_permutation,
    generatedFifth_odd_inverse_phase]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
