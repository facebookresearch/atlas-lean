/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryPacketGeneric

/-! Exact complete whole-word boundary partition into sixteen-prefix blocks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Four complete prefixes retain all twenty-four physical weights and all signed word bits.
/-- Original complete weighted pre and stage-zero equation for one exact prefix block. -/
theorem generatedTenth_packed_boundary_start_0_00_00_quarter_2_block_2 :
    ∀ u : Fin 4,
      (∑ k : Fin 24, generatedTenthTwoFixerTensorNumerator 0 0 k *
        generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryPreWord 0 k
          (generatedTenthPackedBoundaryPacketPrefix 0 ⟨16 * 2 + 4 * 2 + u.val, by omega⟩))) =
        (generatedTenthTwoFixerTensorDenominator 0 : ℤ) *
          generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryStageWord 0 0 0
            (generatedTenthPackedBoundaryPacketPrefix 0 ⟨16 * 2 + 4 * 2 + u.val, by omega⟩)) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
