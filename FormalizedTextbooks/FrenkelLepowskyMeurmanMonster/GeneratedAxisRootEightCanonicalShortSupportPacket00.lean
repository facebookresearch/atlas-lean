/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortSupportPacket00Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortSupportPacket00Block01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortSupportPacket00Block02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortSupportPacket00Block03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightShortSourceBounds

/-! Four complete independent intervals cover the original full short-source packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original nonzero source in the complete packet has its genuine signed canonical image. -/
theorem generatedRootEight_canonical_short_support_packet_00 : ∀ u : Fin 1024,
    generatedRootEightCanonicalShortSupportCondition
      (generatedNinthLowerSpinShortIndex ⟨0 + u.val, by omega⟩) := by
  apply generatedRootEight_short_predicate1024_of_four_blocks
  · intro u
    simpa only [Nat.zero_add, ← Nat.add_assoc] using
      generatedRootEight_canonical_short_support_packet_00_block_00 u
  · intro u
    simpa only [Nat.zero_add, ← Nat.add_assoc] using
      generatedRootEight_canonical_short_support_packet_00_block_01 u
  · intro u
    simpa only [Nat.zero_add, ← Nat.add_assoc] using
      generatedRootEight_canonical_short_support_packet_00_block_02 u
  · intro u
    simpa only [Nat.zero_add, ← Nat.add_assoc] using
      generatedRootEight_canonical_short_support_packet_00_block_03 u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
