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

set_option maxHeartbeats 4000000 in
-- Check all actual original rows in this128-address packet, including every zero row.
/-- Every original row in this packet is covered by the complete signed middle dictionary. -/
theorem generatedNinth_lower_middle_short_rows_covered_packet_27 : ∀ m : Fin 128,
    ∀ h : 3456 + m.val < 4136,
    let k : Fin 4136 := ⟨3456 + m.val, h⟩
    generatedNinthLowerMiddleShortCoefficient (generatedNinthShortRowTarget k) =
      generatedNinthLowerSignedRowNumerator k := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
