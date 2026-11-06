/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTrialityPhaseMerge
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceRootWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddQStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.QCoordinateGenerators

/-! Genuine odd-axis Q fixers merge seven pairs of actual triality root transitions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Seven root indices admitting actual full-axis-fixing phase correction. -/
def generatedAxisGlobalOddPhaseRootIndex : Fin 7 → Fin 9 := ![0, 1, 2, 3, 4, 7, 8]

/-- Original low modulation coordinates chosen to pair oddly with each specified genuine root. -/
def generatedAxisGlobalOddPhaseCoordinate : Fin 7 → Fin 11 := ![0, 0, 0, 1, 1, 0, 4]

/-- Positive original Pauli lifts in the genuine odd-axis stabilizer. -/
def generatedAxisGlobalOddPhaseQ (k : Fin 7) : Q :=
  qCoordinateGenerator (Fin.natAdd 12 (generatedAxisGlobalOddPhaseCoordinate k).castSucc)

set_option maxHeartbeats 1000000 in
-- Check all original support, relative-sign and central-sign conditions on the actual Q lifts.
/-- Every chosen Pauli lift has precisely the three required spin-state fixation parameters. -/
theorem generatedAxisGlobalOddPhaseQ_parameters : ∀ k : Fin 7,
    generatedOddSpinLow (spinTranslation (generatedAxisGlobalOddPhaseQ k)) = 0 ∧
    spinModulation (generatedAxisGlobalOddPhaseQ k) 11 = 0 ∧
    generatedOddSpinOutputSign (generatedAxisGlobalOddPhaseQ k) = 0 := by
  decide +kernel

/-- All chosen original Pauli elements fix the entire actual odd axis. -/
theorem generatedAxisGlobalOddPhaseQ_fixed (k : Fin 7) :
    rhoLocal (inclQ (generatedAxisGlobalOddPhaseQ k)) generatedOddAxis = generatedOddAxis := by
  have hq : generatedAxisGlobalOddPhaseQ k ∈ generatedOddSpinStateStabilizer := by
    change spinOperator _ (generatedOddSpinState 0 1 0) = _
    rw [generatedOddSpinState_pauli,
      (generatedAxisGlobalOddPhaseQ_parameters k).1,
      (generatedAxisGlobalOddPhaseQ_parameters k).2.1,
      (generatedAxisGlobalOddPhaseQ_parameters k).2.2, zero_add]
  exact generatedOddSpinStateStabilizer_le_axis hq

set_option maxHeartbeats 1000000 in
-- Check the exact extraspecial commutator pairing with each original binary root.
/-- Every full-axis fixer pairs oddly with the corresponding genuine norm-eight root. -/
theorem generatedAxisGlobalOddPhaseQ_pairing : ∀ k : Fin 7,
    qBeta (toAdd (generatedAxisGlobalOddPhaseQ k).base)
        (generatedAxisGlobalOddRoot (generatedAxisGlobalOddPhaseRootIndex k)).val +
      qBeta (generatedAxisGlobalOddRoot (generatedAxisGlobalOddPhaseRootIndex k)).val
        (toAdd (generatedAxisGlobalOddPhaseQ k).base) = 1 := by
  decide +kernel

/-- Seven positive and inverse triality transitions lie in the same genuine full local orbit. -/
theorem generatedAxisGlobalOdd_phase_merge (k : Fin 7) :
    ∃ h : H,
      sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
        (generatedAxisGlobalOddPhaseRootIndex k)) generatedOddAxis) =
      rhoLocal h (sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
        (generatedAxisGlobalOddPhaseRootIndex k)) generatedOddAxis)) := by
  apply generatedAxisGlobal_triality_phase_merge generatedOddAxis _ (generatedAxisGlobalOddPhaseQ k)
  · exact generatedAxisGlobalOddPhaseQ_fixed k
  · rw [generatedAxisGlobalOddSourceRootLocalWord_root]
    exact generatedAxisGlobalOddPhaseQ_pairing k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
