/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiSpinInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorExecutable
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitSpatialData

/-! Original integer tensor numerator of the complete Q-corrected conjugated-Xi fiber. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The original cleared raw tensor numerator retains all physical and sixty-four spin terms. -/
def generatedSixthXiRawTensorInteger (n : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ j : Fin 24, sixthFrameOrbitSpatialNumerator 14 i j *
    generatedSixthXiSpinInteger (fun m => generatedSixthTensorExecutable m j) n

/-- The actual Q phase and translation act on the entire original conjugated-Xi numerator. -/
def generatedSixthXiTensorInteger (n : Fin 4096) (i : Fin 24) : ℤ :=
  let t := golayLabelCoefficients n
  let q := generatedSixthGeneratorCorrection 4
  nortonUIntegerSign (spinPhase q t) *
    generatedSixthXiRawTensorInteger (nortonUIntegerLabel (t + spinTranslation q)) i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
