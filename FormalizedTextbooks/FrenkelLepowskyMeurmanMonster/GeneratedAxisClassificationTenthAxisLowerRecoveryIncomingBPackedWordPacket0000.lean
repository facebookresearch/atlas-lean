/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryQuarterGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket0000Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket0000Block01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket0000Block02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedWordPacket0000Block03

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedPacketGeneric

/-! Ungated complete incoming B finite packets; no declaration has passed Lean. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Scope 64 words, retaining 1024 signed slots in each of eight original sources.
/-- Complete original Sj, physical-column and B word equations for this packet. -/
theorem generatedTenth_incoming_B_packed_word_packet_00_00 :
    GeneratedTenthIncomingBPackedWordPacketCondition 0 0 := by
  unfold GeneratedTenthIncomingBPackedWordPacketCondition
  let P : Fin 64 → Prop := fun u => (∑ r : Fin 8, generatedTenthSourceSpatialWordLiteralNumerator 0
      (generatedTwelfthTensorSourceCoordinate r) * generatedRootEightPackedSignedWord
        (generatedTenthIncomingBPackedSourceWord generatedTenthSourceColumnSpinSumCache r
          (generatedTenthIncomingBPackedPacketPrefix 0 u))) =
      4 * generatedRootEightPackedSignedWord
        (generatedTenthIncomingBPackedTargetWord generatedTenthIncomingTensorPackedCache 0
          (generatedTenthIncomingBPackedPacketPrefix 0 u))
  have hP : ∀ q : Fin 4, ∀ v : Fin 16, P ⟨16 * q.val + v.val, by omega⟩ := by
    intro q v
    fin_cases q
    · exact generatedTenth_incoming_B_word_00_00_block_00 v
    · exact generatedTenth_incoming_B_word_00_00_block_01 v
    · exact generatedTenth_incoming_B_word_00_00_block_02 v
    · exact generatedTenth_incoming_B_word_00_00_block_03 v
  intro u
  exact generatedTenth_packed_boundary_quarter_cover P hP u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
