/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortPacket

/-! Exact original finite central phases for the complete actual fifth short packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Candidate original preferred-Q and input Fourier phases of all fifty-six octads. -/
def generatedAxisGlobalFifthShortOctadPhaseData : Fin 56 → ZMod 2 :=
  ![0, 1, 1, 0, 1, 0, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 1, 0, 1, 0, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0,
    1, 1, 1, 1, 1, 1, 1, 1,
    0, 0, 1, 1, 1, 1, 0, 0,
    1, 1, 0, 0, 0, 0, 1, 1]

set_option maxHeartbeats 20000000 in
-- The original inverse word acts on fifty-six full coordinate lifts, retaining central phases.
set_option maxRecDepth 10000 in
/-- Every displayed octad phase is the actual original coefficient phase. -/
theorem generatedAxisGlobalFifthShortOctadPhase_actual (j : Fin 56) :
    generatedFifthEvenCoefficientPhase j = generatedAxisGlobalFifthShortOctadPhaseData j := by
  have h : ∀ j : Fin 56, toAdd (generatedFifthInverseQImage
      (generatedFifthEvenRootQ j)).coeff + generatedFifthEvenRootInputPhase j =
        generatedAxisGlobalFifthShortOctadPhaseData j := by
    decide +kernel
  exact h j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
