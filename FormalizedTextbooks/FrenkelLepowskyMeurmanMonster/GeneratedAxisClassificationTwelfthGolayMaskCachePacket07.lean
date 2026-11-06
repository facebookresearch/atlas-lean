/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGolayMaskCacheData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 8000000 in
-- Verify the complete codeword and original weight phase at every label in this packet.
/-- Every bounded original odd label retains its complete mask and Parker weight sign. -/
theorem generatedTwelfth_golay_mask_cache_packet_07 : ∀ u : Fin 256,
    let d : Fin 2048 := ⟨7 * 256 + u.val, by omega⟩
    generatedTwelfthGolayMaskCache d = golayEncodedMask d.val ∧
      generatedTwelfthGolayPhaseCache d =
        nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
