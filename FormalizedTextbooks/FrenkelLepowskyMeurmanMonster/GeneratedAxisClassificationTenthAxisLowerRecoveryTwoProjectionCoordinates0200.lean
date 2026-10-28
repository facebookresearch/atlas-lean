/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoProjectionGeneric

/-! Eight complete source word columns for original10, block0. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000 in
-- Bound the complete kernel replay of these eight original signed word columns.
/-- Each literal original word column equals its full original twenty-four-bit source. -/
theorem generatedTenth_axis_lower_recovery_two_projection_coordinates_02_00
    (j : Fin 8) :
    generatedTenthAxisLowerRecoveryTwoProjectionMaskWord
      (generatedTenthAxisLowerRecoveryTwoProjectionWords 2) (2 ^ (8 * 0 + j.val)) =
      generatedTenthAxisLowerRecoveryCompactBinaryColumns
        (generatedTenthAxisLowerRecoveryTwoProjectionCandidateIndex 2)
        ⟨8 * 0 + j.val, by omega⟩ := by
  have h : ∀ j : Fin 8,
      generatedTenthAxisLowerRecoveryTwoProjectionMaskWord
        (generatedTenthAxisLowerRecoveryTwoProjectionWords 2) (2 ^ (8 * 0 + j.val)) =
        generatedTenthAxisLowerRecoveryCompactBinaryColumns
          (generatedTenthAxisLowerRecoveryTwoProjectionCandidateIndex 2)
          ⟨8 * 0 + j.val, by omega⟩ := by
    decide +kernel
  exact h j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
