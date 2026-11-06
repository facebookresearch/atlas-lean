/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedSoundness

/-! Original signed permutation on spin-label block 3, chronological step 7. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Bound this exact signed source permutation replay to 256 original labels.
/-- Every coordinate in this block follows the original Parker permutation and phase. -/
theorem generatedNinth_column_packed_permutation_7_packet_03 : ∀ m : Fin 256,
    generatedSixthIntegerPermutationFast 1 (generatedNinthColumnSpinPacked 6)
        ⟨768 + m.val, by omega⟩ =
      generatedNinthColumnSpinPacked 7 ⟨768 + m.val, by omega⟩ := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
