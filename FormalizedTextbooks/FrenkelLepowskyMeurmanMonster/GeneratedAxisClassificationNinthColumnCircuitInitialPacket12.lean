/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnInputSparse

/-! Original column-one input check on chronological spin-label block 12. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Bound the kernel replay to 256 original source labels.
/-- Every coordinate of this block agrees with the original 64-state input sum. -/
theorem generatedNinth_column_initial_packet_12 : ∀ m : Fin 256,
    generatedNinthColumnSpinData 0 ⟨3072 + m.val, by omega⟩ =
      generatedNinthColumnInputSparse 1 ⟨3072 + m.val, by omega⟩ := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
