/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket1700
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket1701
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket1702
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket1703

/-! Ungated complete incoming B finite packets; no declaration has passed Lean. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All four complete packets cover this original physical row. -/
theorem generatedTenth_incoming_B_packed_word_row_17 (b : Fin 4) :
    GeneratedTenthIncomingBPackedWordPacketCondition 17 b := by
  fin_cases b
  · exact generatedTenth_incoming_B_packed_word_packet_17_00
  · exact generatedTenth_incoming_B_packed_word_packet_17_01
  · exact generatedTenth_incoming_B_packed_word_packet_17_02
  · exact generatedTenth_incoming_B_packed_word_packet_17_03

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
