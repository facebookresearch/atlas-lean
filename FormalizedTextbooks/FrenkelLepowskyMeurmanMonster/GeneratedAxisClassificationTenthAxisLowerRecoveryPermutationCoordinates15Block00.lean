/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationGeneric

/-! All original coordinates in one bounded fifteen-entry traversal block. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Verify each complete original word at all twenty-four coordinates in this block.
/-- Every original word retains its entire actual coordinate action. -/
theorem generatedTenth_axis_lower_recovery_traversal_coordinates_15_block00 :
    ∀ u : Fin 15,
      generatedTenthAxisLowerRecoveryEvaluateWord
        (generatedTenthAxisLowerRecoveryTraversalWord ⟨675 + u.val, by omega⟩) =
          generatedTenthAxisLowerRecoveryTraversalForward ⟨675 + u.val, by omega⟩ := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
