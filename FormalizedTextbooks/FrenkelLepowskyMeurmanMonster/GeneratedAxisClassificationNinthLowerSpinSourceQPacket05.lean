/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayCertificates05

/-! One complete source-word full-Q packet, replayed on all original 24 coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Replay the complete primitive source word on all twenty-four full Q coordinates.
/-- Entire original generator 5 word, retaining its full central source phases. -/
theorem generatedNinth_lower_spin_source_q_packet_05 : ∀ j : Fin 24,
    generatedNinthLowerSpinSourceQEvaluation 5 (qCoordinateGenerator j) =
      generatedNinthLowerSpinQImage 5 j := by
  intro j
  exact generatedNinth_lower_spin_source_q_replay_generator_05 j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
