/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedReplayPacket00Part00

/-! Sixteen bounded chronological primitive steps, all full Q coordinate images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

/-- Every actual primitive in this sixteen-step block retains all full central coordinates. -/
theorem generatedNinth_lower_spin_source_q_replay_packet_00_part_00 :
    ∀ n : Fin 16, ∀ j : Fin 24,
      0 + n.val < 174 →
        generatedNinthLowerSpinSourceQReplayStepCondition 0
          ⟨0 + n.val, by omega⟩ j := by
  exact generatedNinth_lower_spin_primitive_packed_replay_packet_00_part_00

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
