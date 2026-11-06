/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthEvenRootLabels
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthEvenRootPhysical
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthOddRootImages
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralizerGeometryShortLines

/-! Actual preferred-root images of the 56 physical octad-root certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators
open Multiplicative

/-- Every checked integer image is the corresponding genuine physical short-vector image. -/
theorem generatedFifth_even_inverse_vector (j : Fin 56) :
    (generatedFifthLocalFiber⁻¹).val.2.val
        (griessShortVector (generatedFifthEvenRootOutputLabel j)) =
      (generatedFifthEvenRootPhysicalSign j : ℝ) •
        griessShortVector (generatedFifthEvenRootInputLabel j) := by
  change (generatedFifthLocalFiber⁻¹).val.2.val
    (fun i => (griessShortIntegral (generatedFifthEvenRootOutputLabel j) i : ℝ) / Real.sqrt 8) = _
  rw [generatedFifth_inverse_normalized_vector]
  funext i
  have hc := generatedFifth_even_inverse_integral_certificate j i
  rw [generatedFifthEvenRootOutputLabel_integral]
  rw [hc]
  simp only [Pi.smul_apply, smul_eq_mul, griessShortVector,
    generatedFifthEvenRootInputLabel_integral, Int.cast_mul, Int.cast_ofNat]
  have hsqrt : Real.sqrt 8 ≠ 0 := by positivity
  field_simp

/-- The genuine inverse preferred-short permutation sends each octad output to its checked input. -/
theorem generatedFifth_even_inverse_permutation (j : Fin 56) :
    griessShortPermutation (generatedFifthLocalFiber⁻¹).val.2
        (generatedFifthEvenRootOutputLabel j) = generatedFifthEvenRootInputLabel j := by
  have h := generatedFifth_even_inverse_vector j
  rcases griessShortPermutation_vector (generatedFifthLocalFiber⁻¹).val.2
    (generatedFifthEvenRootOutputLabel j) with hv | hv
  · exact centralizer_shortVector_line_unique _ _ _ (hv.symm.trans h)
  · apply centralizer_shortVector_line_unique _ _
      (-(generatedFifthEvenRootPhysicalSign j : ℝ))
    simpa only [neg_neg, neg_smul] using congrArg Neg.neg (hv.symm.trans h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
