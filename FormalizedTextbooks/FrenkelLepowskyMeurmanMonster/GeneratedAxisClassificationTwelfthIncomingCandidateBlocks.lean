/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthFullQBlockTransfer

/-! Both complete candidate incoming blocks equal the actual original source blocks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
-- Compare the complete original seven-stage normalization without dropping its word spine.
set_option maxRecDepth 100000

/-- The candidate retains the actual original incoming matrix and signed-short coefficients. -/
theorem generatedTwelfth_incoming_candidate_source_blocks :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
      generatedFifthAxis)).1 = generatedAxisGlobalFifthRoot09Packet.1 ∧
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
      generatedFifthAxis)).2.1 = generatedAxisGlobalFifthRoot09Packet.2.1 := by
  have h := generatedTwelfth_full_Q_matrix_short_blocks generatedTwelfthIncomingCertifiedFiber
    (generatedTenthQWordFiber 9) generatedTwelfth_incoming_spin_compact_oriented_conjugation
    generatedFifthAxis
  rw [generatedTenth_Q_word_fiber_local, generatedAxisGlobalFifthRoot09Packet_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
