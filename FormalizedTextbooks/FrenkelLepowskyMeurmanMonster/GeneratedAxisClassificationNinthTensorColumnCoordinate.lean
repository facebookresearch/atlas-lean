/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnFullSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticReal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTrialityTensor

/-! The final tensor column retains the literal original XYZ action and its two source terms. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual first tensor column with its original denominator cleared. -/
def generatedNinthTensorColumn (t : SpinIndex) : ℝ :=
  64 * Real.sqrt 2 * (griessConwayEncode generatedNinthAxis).2.2 t 1

/-- Original XYZ triality retains both the actual odd-short coefficient and spin difference. -/
theorem generatedNinth_tensor_column_source (t : SpinIndex) :
    generatedNinthTensorColumn t =
      4 * qSign (t 11) *
        (if (golayEncodedMask (spinDictionaryCode t).val).testBit 1 then -1 else 1) *
        (generatedNinthIncomingCoefficient (spinDictionaryCode t) : ℝ) +
      (if (golayEncodedMask (spinDictionaryCode t).val).testBit 1 then -1 else 1) *
        qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) *
        ((generatedNinthColumnSpinData 9
          ⟨(spinDictionaryCode t).val, by omega⟩ : ℝ) -
        (generatedNinthColumnSpinData 9
          ⟨(spinDictionaryCode t).val + 2048, by omega⟩ : ℝ)) := by
  unfold generatedNinthTensorColumn
  rw [generatedNinthAxis_local_expression, generatedSixth_triality_tensor_coordinate]
  simp only [trialityYTensor, ite_true, mul_one]
  rw [show Sum.inr (Sum.inr (spinDictionaryCode t, (1 : Fin 24))) =
      generatedNinthIncomingTargetIndex (spinDictionaryCode t) from rfl,
    generatedNinth_middle_incoming_coefficient,
    generatedNinth_middle_column_full, generatedNinth_middle_column_full]
  simp only [nortonUIntegerLabel_coeff, show (1 : Fin 24).val = 1 from rfl]
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hn]
  ring

/-- Every actual normalized tensor coordinate equals its checked original XYZ integer cache. -/
theorem generatedNinth_tensor_column (t : SpinIndex) :
    generatedNinthTensorColumn t =
      (generatedNinthFinalColumnInteger (nortonUIntegerLabel t) : ℝ) := by
  rw [generatedNinth_tensor_column_source,
    ← generatedNinth_final_column_arithmetic_real, generatedNinth_final_column_arithmetic]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
