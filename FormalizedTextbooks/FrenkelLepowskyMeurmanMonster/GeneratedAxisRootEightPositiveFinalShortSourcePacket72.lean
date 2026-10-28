/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalShortSourcePacket72Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalShortSourcePacket72Block01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalShortSourcePacket72Block02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalShortSourcePacket72Block03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightShortSourceBounds

/-! Independent finite intervals cover the complete original signed source packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 64000000

/-- Every original source coordinate in the full packet equals its exact integer cache. -/
theorem generatedRootEight_positive_final_short_source_packet_72 : ∀ u : Fin 1024,
    generatedRootEightPositiveFinalShortNumerator
      (generatedNinthLowerSpinShortIndex ⟨73728 + u.val, by omega⟩) =
      generatedRootEightPositiveFinalShortCachedNumerator
        (generatedNinthLowerSpinShortIndex ⟨73728 + u.val, by omega⟩) := by
  apply generatedRootEight_short_predicate1024_of_four_blocks
  · intro u
    simpa only [Nat.zero_add, ← Nat.add_assoc] using
      generatedRootEight_positive_final_short_source_packet_72_block_00 u
  · intro u
    simpa only [Nat.zero_add, ← Nat.add_assoc] using
      generatedRootEight_positive_final_short_source_packet_72_block_01 u
  · intro u
    simpa only [Nat.zero_add, ← Nat.add_assoc] using
      generatedRootEight_positive_final_short_source_packet_72_block_02 u
  · intro u
    simpa only [Nat.zero_add, ← Nat.add_assoc] using
      generatedRootEight_positive_final_short_source_packet_72_block_03 u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
