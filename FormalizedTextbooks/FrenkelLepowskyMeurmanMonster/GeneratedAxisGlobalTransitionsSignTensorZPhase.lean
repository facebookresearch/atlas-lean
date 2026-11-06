/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignTensorZ

/-! Executable source polynomial phases of the genuine Golay sign Z-sector action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Exact finite source-code phase on one original Z dictionary vector. -/
def generatedAxisGlobalSignZPhase (a : Fin 4096) (d : Fin 2048) (i : Fin 24) : ZMod 2 :=
  spinDot (golayLabelCoefficients a) (sourceWordTheta ⟨d.val, by omega⟩) +
    spinDot (golayLabelCoefficients a) (fun k => (golayGeneratorBit k i : ZMod 2)) +
    spinDot (golayLabelCoefficients ⟨d.val, by omega⟩) (sourceWordTheta a)

/-- The actual preferred-Q phase reduces to the explicit finite source polynomial. -/
theorem generatedAxisGlobalSignZPhase_eq (a : Fin 4096) (ε : ZMod 2)
    (d : Fin 2048) (i : Fin 24) :
    localShortPhase (localFiberIncl (sourceQCode a ε)) (Sum.inr (Sum.inr (d, i))) =
      generatedAxisGlobalSignZPhase a d i := by
  rw [localAxisQPhase_eq_short_phase]
  change qBeta (Multiplicative.toAdd (sourceQCode a ε).base)
      (Multiplicative.toAdd (griessShortQ (Sum.inr (Sum.inr (d, i)))).base) +
    qBeta (Multiplicative.toAdd (griessShortQ (Sum.inr (Sum.inr (d, i)))).base)
      (Multiplicative.toAdd (sourceQCode a ε).base) = _
  rw [qBeta_spin_coordinates, qBeta_spin_coordinates, sourceQCode_translation,
    sourceQCode_modulation, griessOdd_translation, griessOdd_modulation,
    ← sourceWordTheta_polynomial]
  rw [spinDot_add_right, spinDot_add_left]
  rw [spinDot_comm (griessOddOmegaCoefficient d i • (Pi.single 11 1 : SpinIndex))
    (sourceWordTheta a), spinDot_smul_right, sourceWordTheta_dot_omega, mul_zero, add_zero]
  rfl

/-- The actual full tensor operator has the executable original source Z-sector phase. -/
theorem generatedAxisGlobalSign_tensor_Z_polynomial (a : Fin 4096) (ε : ZMod 2)
    (d : Fin 2048) (i : Fin 24) :
    localTensorRepresentation (generatedFifthSignFiber a ε) (trialityZTensor d i) =
      qSign (generatedAxisGlobalSignZPhase a d i) • trialityZTensor d i := by
  rw [generatedAxisGlobalSign_tensor_Z, generatedAxisGlobalSignZPhase_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
