/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingShortData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- This bounded source packet checks64 complete original row addresses and coefficients.
/-- The bounded packet preserves every original source row and its full central sign. -/
theorem generatedTwelfth_incoming_short_key_check00 : ∀ i : Fin 64,
    let a : Fin 3856 := ⟨(0 + i.val) % 3856, Nat.mod_lt _ (by decide)⟩
    generatedTwelfthIncomingShortKey a =
      generatedNinthLowerShortAddress
        (generatedTwelfthIncomingShortTarget (generatedTwelfthIncomingShortRow a)) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
