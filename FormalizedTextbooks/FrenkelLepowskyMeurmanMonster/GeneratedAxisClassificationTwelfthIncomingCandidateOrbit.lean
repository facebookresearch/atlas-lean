/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCertifiedMatrixBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthFullQProjectionTransfer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthRepresentative

/-! A complete genuine compact incoming candidate retains the original axis orbit
and projections. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
-- Elaborating the complete original seven-stage source word retains its full spine.
set_option maxRecDepth 100000

/-- The complete candidate axis uses genuine triality on its genuine certified incoming fiber. -/
def generatedTwelfthIncomingCandidateAxis : GriessSpace :=
  sExtra (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber) generatedFifthAxis)

/-- Every candidate fixer provides an actual original-axis fixer with exactly the same projection. -/
theorem generatedTwelfth_incoming_candidate_fixer_transfer (h : H)
    (hfix : rhoLocal h generatedTwelfthIncomingCandidateAxis =
      generatedTwelfthIncomingCandidateAxis) :
    ∃ k : H, projH k = projH h ∧ rhoLocal k generatedTwelfthAxis = generatedTwelfthAxis := by
  have he : spinConjugation (generatedTenthQWordFiber 9).val.1 =
      spinConjugation generatedTwelfthIncomingCertifiedFiber.val.1 :=
    generatedTwelfth_incoming_spin_compact_oriented_conjugation.symm
  obtain ⟨k, hk, haxis⟩ := generatedTwelfth_full_Q_triality_fixer_transfer
    (generatedTenthQWordFiber 9) generatedTwelfthIncomingCertifiedFiber he generatedFifthAxis h hfix
  refine ⟨k, hk, ?_⟩
  rw [generatedTenth_Q_word_fiber_local] at haxis
  exact haxis

/-- The original genuine axis is an actual local orbit image of the complete certified candidate. -/
theorem generatedTwelfth_incoming_candidate_local_orbit :
    ∃ h : H, projH h = 1 ∧ generatedTwelfthAxis =
      rhoLocal h generatedTwelfthIncomingCandidateAxis := by
  have he : spinConjugation (generatedTenthQWordFiber 9).val.1 =
      spinConjugation generatedTwelfthIncomingCertifiedFiber.val.1 :=
    generatedTwelfth_incoming_spin_compact_oriented_conjugation.symm
  obtain ⟨h, hh, haxis⟩ := generatedTwelfth_full_Q_triality_projection_orbit
    (generatedTenthQWordFiber 9) generatedTwelfthIncomingCertifiedFiber he generatedFifthAxis
  rw [generatedTenth_Q_word_fiber_local] at haxis
  exact ⟨h, hh, haxis⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
