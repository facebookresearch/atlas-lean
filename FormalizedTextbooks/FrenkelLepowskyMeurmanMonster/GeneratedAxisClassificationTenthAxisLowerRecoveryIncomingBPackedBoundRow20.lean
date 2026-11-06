/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedBoundPacket2000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedBoundPacket2001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedBoundPacket2002
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedBoundPacket2003

/-! Ungated complete incoming B finite packets; no declaration has passed Lean. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All four complete packets cover this original physical row. -/
theorem generatedTenth_incoming_B_packed_bound_row_20 (b : Fin 4) :
    GeneratedTenthIncomingBPackedBoundPacketCondition 20 b := by
  fin_cases b
  · exact generatedTenth_incoming_B_packed_bound_packet_20_00
  · exact generatedTenth_incoming_B_packed_bound_packet_20_01
  · exact generatedTenth_incoming_B_packed_bound_packet_20_02
  · exact generatedTenth_incoming_B_packed_bound_packet_20_03

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
