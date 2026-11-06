/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneSpinBitSignsData

/-! All compact signs are checked against the genuine original spin operators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The complete original 4096-label diagonal sign is checked in the ordinary kernel.
/-- The packed Gaussian signs are exactly the original diagonal cocode Gaussian. -/
theorem generatedSeventhXiPlaneBitGamma_actual : ∀ d : Fin 4096,
    nortonUIntegerGammaSign (golayLabelCoefficients d) = generatedSeventhXiPlaneBitGamma d := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Every phase retains the genuine central coefficient of the Pauli correction.
/-- The compact correction signs equal the complete actual extraspecial phases. -/
theorem generatedSeventhXiPlaneBitCorrectionPhase_actual : ∀ d : Fin 4096,
    nortonUIntegerSign (spinPhase generatedSeventhXiPlaneCorrection
      (golayLabelCoefficients d)) = generatedSeventhXiPlaneBitCorrectionPhase d := by
  decide +kernel

/-- The actual correction translates spin labels by the literal twelve-bit value 1804. -/
theorem generatedSeventhXiPlaneBitCorrection_translation :
    nortonUIntegerLabel (spinTranslation generatedSeventhXiPlaneCorrection) = 1804 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
