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

/-! Seven genuine fifth binary roots admit the same literal full-axis-fixing
phase correction. Their two real triality transports need only one local class binding. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Exact root indices whose Ω sign is flipped by the actual modulation-48 axis fixer. -/
def generatedAxisGlobalFifthMergedRoot : Fin 7 → Fin 14 := ![2, 3, 4, 5, 8, 9, 10]

set_option maxHeartbeats 1000000 in
-- Check all seven actual binary roots against the original phase-correct Q candidate.
/-- One genuine full-axis fixer has odd pairing with each listed original root. -/
theorem generatedAxisGlobalFifthMergedRoot_pairing : ∀ j : Fin 7,
    qBeta (toAdd (generatedFifthQCandidate 0 1).base)
        (generatedAxisGlobalFifthRoot (generatedAxisGlobalFifthMergedRoot j)).val +
      qBeta (generatedAxisGlobalFifthRoot (generatedAxisGlobalFifthMergedRoot j)).val
        (toAdd (generatedFifthQCandidate 0 1).base) = 1 := by
  decide +kernel

/-- Both actual triality signs at these seven roots have the same full-vector local orbit. -/
theorem generatedAxisGlobalFifthMergedRoot_orbit (j : Fin 7) :
    ∃ k : H,
      sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord
        (generatedAxisGlobalFifthMergedRoot j)) generatedFifthAxis) =
      rhoLocal k (sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord
        (generatedAxisGlobalFifthMergedRoot j)) generatedFifthAxis)) := by
  apply generatedAxisGlobal_triality_phase_merge _ _ (generatedFifthQCandidate 0 1)
  · exact generatedFifth_candidate_full_fixed 0 1
  · rw [generatedAxisGlobalFifthShortLocalWord_root]
    exact generatedAxisGlobalFifthMergedRoot_pairing j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
