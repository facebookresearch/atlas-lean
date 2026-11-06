/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationGeneric

/-! Complete full 24-coordinate checks for original traversal entries270 through314. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Check every original word and all twenty-four coordinates in this bounded block.
/-- Every original word in this 45-entry block retains all 24 actual coordinates. -/
theorem generatedTenth_axis_lower_recovery_traversal_coordinates_06 :
    ∀ u : Fin 45,
      generatedTenthAxisLowerRecoveryEvaluateWord
        (generatedTenthAxisLowerRecoveryTraversalWord ⟨270 + u.val, by omega⟩) =
          generatedTenthAxisLowerRecoveryTraversalForward ⟨270 + u.val, by omega⟩ := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
