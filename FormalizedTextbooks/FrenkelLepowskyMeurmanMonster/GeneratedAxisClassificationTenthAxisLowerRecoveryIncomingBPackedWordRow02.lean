/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket0200
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket0201
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket0202
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket0203

/-! Ungated complete incoming B finite packets; no declaration has passed Lean. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All four complete packets cover this original physical row. -/
theorem generatedTenth_incoming_B_packed_word_row_02 (b : Fin 4) :
    GeneratedTenthIncomingBPackedWordPacketCondition 2 b := by
  fin_cases b
  · exact generatedTenth_incoming_B_packed_word_packet_02_00
  · exact generatedTenth_incoming_B_packed_word_packet_02_01
  · exact generatedTenth_incoming_B_packed_word_packet_02_02
  · exact generatedTenth_incoming_B_packed_word_packet_02_03

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
