/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPackedPacket00Part00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortSupportData

/-! The existing complete full-Q packet also covers all of its nonzero sources. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every nonzero source in this packet retains its full checked preferred-Q image. -/
theorem generatedNinth_lower_spin_short_support_packet_00_part_00 : ∀ a : Fin 8192,
    if h : 0 * 8192 + a.val < 98280 then
      generatedNinthLowerSpinShortSupportCondition 0
        ⟨0 * 8192 + a.val, h⟩ else True := by
  intro a
  have ha : 0 * 8192 + a.val < 98280 := by omega
  rw [dite_eq_left ha]
  intro _
  have hp := generatedNinth_lower_spin_short_packed_packet_00_part_00 a
  rw [dite_eq_left ha] at hp
  exact hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
