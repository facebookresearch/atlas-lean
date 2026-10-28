/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationInverseData

/-! Exact inverse lookup for original entries 0 through 44. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Check every original entry in this complete 45-entry block.
/-- All 45 original indices have their exact full inverse lookup roundtrip. -/
theorem generatedTenth_axis_lower_recovery_inverse_coordinates_00 :
    ∀ u : Fin 45, generatedTenthAxisLowerRecoveryPermutationInverseLookup
      (generatedTenthAxisLowerRecoveryPermutationKey ⟨0 + u.val, by omega⟩) =
        some (⟨0 + u.val, by omega⟩ : Fin 720) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
