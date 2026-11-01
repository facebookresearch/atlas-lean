/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthEvenRootLabels
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthOddRootImages
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralizerGeometryShortLines

/-! Actual preferred-root images of the 63 physical octad-root certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators
open Multiplicative

/-- Every checked integer image is the corresponding genuine physical short-vector image. -/
theorem generatedFourth_even_inverse_vector (j : Fin 63) :
    (generatedFourthLocalFiber⁻¹).val.2.val
        (griessShortVector (generatedFourthEvenRootOutputLabel j)) =
      (generatedFourthEvenRootPhysicalSign j : ℝ) •
        griessShortVector (generatedFourthEvenRootInputLabel j) := by
  change (generatedFourthLocalFiber⁻¹).val.2.val
    (fun i => (griessShortIntegral (generatedFourthEvenRootOutputLabel j) i : ℝ) / Real.sqrt 8) = _
  rw [generatedFourth_inverse_normalized_vector]
  funext i
  have hc := generatedFourth_even_inverse_integral_certificate j i
  rw [generatedFourthEvenRootOutputLabel_integral]
  rw [hc]
  simp only [Pi.smul_apply, smul_eq_mul, griessShortVector,
    generatedFourthEvenRootInputLabel_integral, Int.cast_mul, Int.cast_ofNat]
  have hsqrt : Real.sqrt 8 ≠ 0 := by positivity
  field_simp

/-- The genuine inverse preferred-short permutation sends each octad output to its checked input. -/
theorem generatedFourth_even_inverse_permutation (j : Fin 63) :
    griessShortPermutation (generatedFourthLocalFiber⁻¹).val.2
        (generatedFourthEvenRootOutputLabel j) = generatedFourthEvenRootInputLabel j := by
  have h := generatedFourth_even_inverse_vector j
  rcases griessShortPermutation_vector (generatedFourthLocalFiber⁻¹).val.2
    (generatedFourthEvenRootOutputLabel j) with hv | hv
  · exact centralizer_shortVector_line_unique _ _ _ (hv.symm.trans h)
  · apply centralizer_shortVector_line_unique _ _
      (-(generatedFourthEvenRootPhysicalSign j : ℝ))
    simpa only [neg_neg, neg_smul] using congrArg Neg.neg (hv.symm.trans h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
