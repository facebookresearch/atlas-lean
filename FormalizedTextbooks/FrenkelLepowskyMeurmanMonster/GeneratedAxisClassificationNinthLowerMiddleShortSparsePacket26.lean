/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerMiddleShortData

/-! Exact original middle dictionary checks in bounded128-row packets. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Check all actual sparse rows in this128-address packet with no omitted entry.
/-- Every original sparse entry in this packet has its full exact key target. -/
theorem generatedNinth_lower_middle_short_key_target_packet_26 : ∀ m : Fin 128,
    ∀ h : 3328 + m.val < 3856,
    let a : Fin 3856 := ⟨3328 + m.val, h⟩
    generatedNinthLowerMiddleShortKey a = generatedNinthLowerShortAddress
      (generatedNinthShortRowTarget (generatedNinthLowerMiddleShortRow a)) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check all actual sparse rows in this128-address packet with no omitted entry.
/-- Every original sparse entry in this packet has its full exact row numerator. -/
theorem generatedNinth_lower_middle_short_row_numerator_packet_26 : ∀ m : Fin 128,
    ∀ h : 3328 + m.val < 3856,
    let a : Fin 3856 := ⟨3328 + m.val, h⟩
    generatedNinthLowerMiddleShortNumerator a =
      generatedNinthLowerSignedRowNumerator (generatedNinthLowerMiddleShortRow a) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
