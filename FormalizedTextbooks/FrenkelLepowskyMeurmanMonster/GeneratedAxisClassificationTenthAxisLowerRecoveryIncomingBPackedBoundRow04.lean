/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedBoundPacket0400
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedBoundPacket0401
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedBoundPacket0402
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedBoundPacket0403

/-! Ungated complete incoming B finite packets; no declaration has passed Lean. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All four complete packets cover this original physical row. -/
theorem generatedTenth_incoming_B_packed_bound_row_04 (b : Fin 4) :
    GeneratedTenthIncomingBPackedBoundPacketCondition 4 b := by
  fin_cases b
  · exact generatedTenth_incoming_B_packed_bound_packet_04_00
  · exact generatedTenth_incoming_B_packed_bound_packet_04_01
  · exact generatedTenth_incoming_B_packed_bound_packet_04_02
  · exact generatedTenth_incoming_B_packed_bound_packet_04_03

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
