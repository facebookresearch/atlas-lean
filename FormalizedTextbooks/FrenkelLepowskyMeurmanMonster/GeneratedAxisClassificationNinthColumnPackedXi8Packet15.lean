/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedGamma

/-! Original Gaussian numerator on spin-label block 15, chronological step 8. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Bound this exact 64-term Gaussian replay to 256 original spin labels.
/-- Every original Gaussian coordinate in this block has the certified next numerator. -/
theorem generatedNinth_column_packed_xi_8_packet_15 : ∀ m : Fin 256,
    generatedNinthColumnXiPacked (generatedNinthColumnSpinPacked 7)
        ⟨3840 + m.val, by omega⟩ =
      16 * generatedNinthColumnSpinPacked 8 ⟨3840 + m.val, by omega⟩ := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
