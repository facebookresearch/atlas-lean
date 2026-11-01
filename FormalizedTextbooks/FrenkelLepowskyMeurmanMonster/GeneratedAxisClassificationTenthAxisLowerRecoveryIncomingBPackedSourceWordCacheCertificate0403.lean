/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedSourceWordCacheData04

/-! Complete original signed source-word equality on one independent 64-prefix leaf. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
-- Complete sixteen-slot original source words need a deeper finite recursion limit.
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks exactly one source column and 64 original word prefixes.
/-- Every original signed source slot and zero is retained in this exact word equality. -/
theorem generatedTenth_incoming_B_source_word_cache_certificate_04_03 : ∀ u : Fin 64,
    generatedTenthIncomingBPackedSourceWord generatedTenthSourceColumnSpinSumCache
      ⟨4, by omega⟩ (generatedTenthIncomingBSourceWordCachePrefix ⟨3, by omega⟩ u) =
        generatedTenthIncomingBSourceWordCache04
          (generatedTenthIncomingBSourceWordCachePrefix ⟨3, by omega⟩ u) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
