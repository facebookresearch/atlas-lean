/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQReplayPacket00Part03

/-! Reuse the checked full original384 source obligations from the exact fast replay leaf. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_00_part_03 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      48 + n.val < 174 →
        generatedNinthLowerSpinSourceQReplayStepCondition 0
          ⟨48 + n.val, by omega⟩ j :=
  generatedNinth_lower_spin_fast_q_replay_packet_00_part_03

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
