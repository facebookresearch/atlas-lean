/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket1100
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket1101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket1102
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket1103

/-! Ungated complete incoming B finite packets; no declaration has passed Lean. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All four complete packets cover this original physical row. -/
theorem generatedTenth_incoming_B_packed_word_row_11 (b : Fin 4) :
    GeneratedTenthIncomingBPackedWordPacketCondition 11 b := by
  fin_cases b
  · exact generatedTenth_incoming_B_packed_word_packet_11_00
  · exact generatedTenth_incoming_B_packed_word_packet_11_01
  · exact generatedTenth_incoming_B_packed_word_packet_11_02
  · exact generatedTenth_incoming_B_packed_word_packet_11_03

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
