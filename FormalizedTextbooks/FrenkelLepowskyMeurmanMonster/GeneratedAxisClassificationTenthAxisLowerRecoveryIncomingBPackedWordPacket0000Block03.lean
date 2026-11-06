/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedPacketGeneric

/-! Ungated complete incoming B finite packets; no declaration has passed Lean. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Check sixteen independent prefixes with all signed source slots and zero terms retained.
/-- This exact part retains all eight original physical source columns. -/
theorem generatedTenth_incoming_B_word_00_00_block_03 :
    ∀ u : Fin 16, (∑ r : Fin 8, generatedTenthSourceSpatialWordLiteralNumerator 0
      (generatedTwelfthTensorSourceCoordinate r) * generatedRootEightPackedSignedWord
        (generatedTenthIncomingBPackedSourceWord generatedTenthSourceColumnSpinSumCache r
          (generatedTenthIncomingBPackedPacketPrefix 0 ⟨16 * 3 + u.val, by omega⟩))) =
      4 * generatedRootEightPackedSignedWord
        (generatedTenthIncomingBPackedTargetWord generatedTenthIncomingTensorPackedCache 0
          (generatedTenthIncomingBPackedPacketPrefix 0 ⟨16 * 3 + u.val, by omega⟩)) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
