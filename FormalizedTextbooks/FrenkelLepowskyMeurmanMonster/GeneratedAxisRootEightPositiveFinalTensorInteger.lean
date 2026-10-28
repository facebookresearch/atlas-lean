/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingPositiveTensorInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalTensorNumeratorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTrialityTensor

/-! The actual final triality tensor retains both original XYZ contributions and their phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual final tensor coordinate has its full integer numerator over 128 root two. -/
theorem generatedRootEight_positive_final_tensor_integer (n : Fin 4096) (i : Fin 24) :
    (griessConwayEncode generatedRootEightIncomingPositiveTrialityDestination).2.2
      (golayLabelCoefficients n) i =
      (generatedRootEightPositiveFinalTensorNumerator n i : ℝ) /
        (128 * Real.sqrt 2) := by
  rw [generatedRootEightIncomingPositiveTrialityDestination,
    generatedSixth_triality_tensor_coordinate,
    generatedRootEight_incoming_positive_short_integer,
    generatedRootEight_incoming_positive_tensor_integer,
    generatedRootEight_incoming_positive_tensor_integer,
    nortonUIntegerLabel_coeff, nortonUIntegerLabel_coeff]
  simp only [trialityYTensor, ite_true, mul_one,
    generatedRootEightPositiveFinalTensorNumerator, Int.cast_add, Int.cast_mul,
    Int.cast_sub, Int.cast_ofNat, nortonUIntegerSign_real,
    Int.cast_ite, Int.cast_neg, Int.cast_one]
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hn]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
