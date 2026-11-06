/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTrialityPhaseMerge
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortInputs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQFull

/-! A literal phase-correct full fifth-axis Q fixer merges both signs at root five. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000 in
-- Evaluate one genuine Q candidate against the exact 24-coordinate norm-eight root.
/-- The phase-correct modulation-48 fixer has odd commutator pairing with root five. -/
theorem generatedAxisGlobalFifthRoot05_odd_pairing :
    qBeta (toAdd (generatedFifthQCandidate 0 1).base) (generatedAxisGlobalFifthRoot 5).val +
      qBeta (generatedAxisGlobalFifthRoot 5).val
        (toAdd (generatedFifthQCandidate 0 1).base) = 1 := by
  decide +kernel

/-- The two actual triality powers at root five lie in the same genuine local orbit. -/
theorem generatedAxisGlobalFifthRoot05_phase_merge :
    ∃ k : H, sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 5) generatedFifthAxis) =
      rhoLocal k (sExtra⁻¹
        (rhoLocal (generatedAxisGlobalFifthShortLocalWord 5) generatedFifthAxis)) := by
  apply generatedAxisGlobal_triality_phase_merge _ _ (generatedFifthQCandidate 0 1)
  · exact generatedFifth_candidate_full_fixed 0 1
  · rw [generatedAxisGlobalFifthShortLocalWord_root]
    exact generatedAxisGlobalFifthRoot05_odd_pairing

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
