/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortSupportPackedData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortPackedPacket00Part00

/-! The preserved original full packet supplies every required nonzero source certificate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Reuse every completed original source check without repeating its kernel evaluation. -/
theorem generatedTwelfth_complete_short_support_packed_packet_00_part_00 : ∀ a : Fin 8192,
    if h : 0 * 8192 + a.val < 98280 then
      generatedTwelfthCompleteShortSupportPackedCondition 0 ⟨0 * 8192 + a.val, h⟩ else True := by
  intro a
  have hh := generatedTwelfth_complete_short_packed_packet_00_part_00 a
  have h : 0 * 8192 + a.val < 98280 := by omega
  simp only [dite_eq_left h]
  unfold generatedTwelfthCompleteShortSupportPackedCondition
  intro _
  simpa only [dite_eq_left h] using hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
