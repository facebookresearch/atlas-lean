/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortSupportPacket95Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortSupportPacket95Block01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortSupportPacket95Block02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortSupportPacket95Block03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightShortSourceBounds

/-! Independent finite intervals cover the complete original signed source packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 64000000

/-- Every original nonzero source in the complete packet has its genuine signed canonical image. -/
theorem generatedRootEight_canonical_short_support_packet_95 : ∀ u : Fin 1000,
    generatedRootEightCanonicalShortSupportCondition
      (generatedNinthLowerSpinShortIndex ⟨97280 + u.val, by omega⟩) := by
  apply generatedRootEight_short_predicate1000_of_blocks
  · intro u
    simpa only [← Nat.add_assoc] using
      generatedRootEight_canonical_short_support_packet_95_block_00 u
  · intro u
    simpa only [← Nat.add_assoc] using
      generatedRootEight_canonical_short_support_packet_95_block_01 u
  · intro u
    simpa only [← Nat.add_assoc] using
      generatedRootEight_canonical_short_support_packet_95_block_02 u
  · intro u
    simpa only [← Nat.add_assoc] using
      generatedRootEight_canonical_short_support_packet_95_block_03 u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
