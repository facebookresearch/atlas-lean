/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionGeneric

/-! Eight complete original binary word columns for candidate5, block0. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000 in
-- Bound the complete kernel replay of these eight original signed word columns.
/-- Each literal original word column equals its full original twenty-four-bit source. -/
theorem generatedTenth_axis_lower_recovery_three_projection_coordinates_05_00
    (j : Fin 8) :
    generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
      (generatedTenthAxisLowerRecoveryThreeProjectionWords 5)
        (2 ^ (8 * 0 + j.val)) =
      generatedTenthAxisLowerRecoveryCompactBinaryColumns 5
        ⟨8 * 0 + j.val, by omega⟩ := by
  have h : ∀ j : Fin 8,
      generatedTenthAxisLowerRecoveryThreeProjectionMaskWord
        (generatedTenthAxisLowerRecoveryThreeProjectionWords 5)
          (2 ^ (8 * 0 + j.val)) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns 5
          ⟨8 * 0 + j.val, by omega⟩ := by
    decide +kernel
  exact h j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
