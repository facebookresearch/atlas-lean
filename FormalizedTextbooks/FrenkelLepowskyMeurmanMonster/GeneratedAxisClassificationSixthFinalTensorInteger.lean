/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOddPacked
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinAnchor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTrialityTensor

/-! A complete exact integer formula for the actual original sixth-axis tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original tensor numerator retains both the incoming Y row
and preferred odd-short row. -/
def generatedSixthFinalTensorNumerator (n : Fin 4096) (j : Fin 24) : ℤ :=
  let t := golayLabelCoefficients n
  let d := spinDictionaryCode t
  let s : ℤ := if (golayEncodedMask d.val).testBit j.val then -1 else 1
  8 * nortonUIntegerSign (t 11) * s * generatedSixthMiddleOddPackedNumerator d j -
    nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) * s *
      generatedSixthFrameVectorData 8 0 j *
        (generatedSixthPartialPhaseInteger 8 ⟨d.val, by omega⟩ -
          generatedSixthPartialPhaseInteger 8 ⟨d.val + 2048, by omega⟩)

/-- Every actual sixth-axis tensor coordinate equals the complete original integer formula. -/
theorem generatedSixth_final_tensor_integer (n : Fin 4096) (j : Fin 24) :
    (griessConwayEncode generatedSixthAxis).2.2 (golayLabelCoefficients n) j =
      (generatedSixthFinalTensorNumerator n j : ℝ) / (32 * Real.sqrt 2) := by
  rw [generatedSixthAxis_local_expression, generatedSixth_triality_tensor_coordinate,
    generatedSixth_middle_odd_packed_coefficient]
  simp_rw [generatedSixth_middle_tensor_integer, nortonUIntegerLabel_coeff,
    generatedSixth_spin_numerator_phase]
  simp only [trialityYTensor, ite_true, mul_one]
  dsimp only [generatedSixthFinalTensorNumerator]
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_sub, nortonUIntegerSign_real,
    Int.cast_ite, Int.cast_neg, Int.cast_one]
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hn]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
