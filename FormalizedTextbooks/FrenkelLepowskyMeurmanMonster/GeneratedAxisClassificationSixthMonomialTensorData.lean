/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorExecutable

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSpinData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalTensorPacked
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitGenerators

/-! Complete signed integer expressions for the actual corrected monomial tensor checks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual physical monomial addresses in the frozen original source-word action. -/
def generatedSixthMonomialPhysicalInput (k : Fin 4) (i : Fin 24) : Fin 24 :=
  sixthFrameOrbitSpatialInput ⟨10 + k.val, by omega⟩ i

/-- Complete signed numerator for a corrected original monomial tensor coordinate. -/
def generatedSixthMonomialTensorNumerator (k : Fin 4) (n : Fin 4096) (i : Fin 24) : ℤ :=
  let t := golayLabelCoefficients n
  let q := generatedSixthGeneratorCorrection (Fin.castAdd 1 k)
  let u := t + spinTranslation q
  let model := generatedSixthMonomialSpinModel k
  nortonUIntegerSign (spinPhase q t + monsterMonomialQuadratic model.phase u) *
    generatedSixthFinalTensorPackedNumerator (nortonUIntegerLabel (model.coordinate *ᵥ u))
      (generatedSixthMonomialPhysicalInput k i)

/-- Executable complete signed numerator for a corrected original monomial tensor coordinate. -/
def generatedSixthMonomialTensorExecutable (k : Fin 4) (n : Fin 4096) (i : Fin 24) : ℤ :=
  let t := golayLabelCoefficients n
  let q := generatedSixthGeneratorCorrection (Fin.castAdd 1 k)
  let u := t + spinTranslation q
  let model := generatedSixthMonomialSpinModel k
  nortonUIntegerSign (spinPhase q t + monsterMonomialQuadratic model.phase u) *
    generatedSixthTensorExecutable (nortonUIntegerLabel (model.coordinate *ᵥ u))
      (generatedSixthMonomialPhysicalInput k i)

/-- Eliminating the selector changes no genuine corrected tensor coefficient. -/
theorem generatedSixth_monomial_tensor_executable_eq (k : Fin 4)
    (n : Fin 4096) (i : Fin 24) :
    generatedSixthMonomialTensorExecutable k n i = generatedSixthMonomialTensorNumerator k n i := by
  simp only [generatedSixthMonomialTensorExecutable, generatedSixthMonomialTensorNumerator,
    generatedSixth_tensor_executable_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
