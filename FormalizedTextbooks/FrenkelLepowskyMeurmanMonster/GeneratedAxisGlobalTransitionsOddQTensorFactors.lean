/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensorResidualLocalCoordinates

/-! The complete original extraspecial tensor correction, with its central spin phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The genuine signed translation on every physical integer spin coordinate. -/
def generatedAxisGlobalOddQSpinInteger (q : Q) (u : Fin 4096 → ℤ)
    (k : Fin 4096) : ℤ :=
  generatedAxisGlobalIntSign (spinPhase q (golayLabelCoefficients k)) *
    u (generatedAxisGlobalSpinLabel (golayLabelCoefficients k + spinTranslation q))

/-- The entire local extraspecial correction preserves the spatial factor and all spin signs. -/
theorem generatedAxisGlobalOddQTensorFactor_actual (q : Q)
    (u : Fin 4096 → ℤ) (v : Fin 24 → ℤ) (D : ℕ) :
    localTensorRepresentation (localFiberIncl q)
        (generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor u v) D) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor (generatedAxisGlobalOddQSpinInteger q u) v) D := by
  funext t i
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  rw [localFiberQ_tensor_columns]
  change qSign (spinPhase q (golayLabelCoefficients k)) *
    generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor u v) D
      (golayLabelCoefficients k + spinTranslation q) i = _
  simp only [generatedAxisGlobalTensorIntegerPacket,
    generatedAxisGlobalOddTensorFactor, generatedAxisGlobalSpinLabel_coeff,
    generatedAxisGlobalOddQSpinInteger, Int.cast_mul, generatedAxisGlobalIntSign_real]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
