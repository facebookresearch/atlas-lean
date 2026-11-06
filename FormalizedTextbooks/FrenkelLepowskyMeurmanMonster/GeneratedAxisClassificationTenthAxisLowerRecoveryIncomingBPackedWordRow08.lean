/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket0800
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket0801
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket0802
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket0803

/-! Ungated complete incoming B finite packets; no declaration has passed Lean. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All four complete packets cover this original physical row. -/
theorem generatedTenth_incoming_B_packed_word_row_08 (b : Fin 4) :
    GeneratedTenthIncomingBPackedWordPacketCondition 8 b := by
  fin_cases b
  · exact generatedTenth_incoming_B_packed_word_packet_08_00
  · exact generatedTenth_incoming_B_packed_word_packet_08_01
  · exact generatedTenth_incoming_B_packed_word_packet_08_02
  · exact generatedTenth_incoming_B_packed_word_packet_08_03

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
