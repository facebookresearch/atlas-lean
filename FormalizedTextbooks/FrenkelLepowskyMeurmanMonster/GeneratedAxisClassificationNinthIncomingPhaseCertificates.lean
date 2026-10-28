/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket26
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket27
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket28
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket29
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket30
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhasePacket31

/-! All original incoming odd-column phase packets have their exact source meaning. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem blocks (k : Fin 32) (m : Fin 64) :
    let d : Fin 2048 := ⟨64 * k.val + m.val, by omega⟩
    generatedNinthIncomingShortNumerator (generatedNinthIncomingSource d) ≠ 0 →
      Multiplicative.toAdd (generatedNinthQImage
        (generatedNinthIncomingShortQ (generatedNinthIncomingSource d))).coeff =
          generatedNinthIncomingPhase d := by
  fin_cases k
  · exact generatedNinth_incoming_phase_packet_00 m
  · exact generatedNinth_incoming_phase_packet_01 m
  · exact generatedNinth_incoming_phase_packet_02 m
  · exact generatedNinth_incoming_phase_packet_03 m
  · exact generatedNinth_incoming_phase_packet_04 m
  · exact generatedNinth_incoming_phase_packet_05 m
  · exact generatedNinth_incoming_phase_packet_06 m
  · exact generatedNinth_incoming_phase_packet_07 m
  · exact generatedNinth_incoming_phase_packet_08 m
  · exact generatedNinth_incoming_phase_packet_09 m
  · exact generatedNinth_incoming_phase_packet_10 m
  · exact generatedNinth_incoming_phase_packet_11 m
  · exact generatedNinth_incoming_phase_packet_12 m
  · exact generatedNinth_incoming_phase_packet_13 m
  · exact generatedNinth_incoming_phase_packet_14 m
  · exact generatedNinth_incoming_phase_packet_15 m
  · exact generatedNinth_incoming_phase_packet_16 m
  · exact generatedNinth_incoming_phase_packet_17 m
  · exact generatedNinth_incoming_phase_packet_18 m
  · exact generatedNinth_incoming_phase_packet_19 m
  · exact generatedNinth_incoming_phase_packet_20 m
  · exact generatedNinth_incoming_phase_packet_21 m
  · exact generatedNinth_incoming_phase_packet_22 m
  · exact generatedNinth_incoming_phase_packet_23 m
  · exact generatedNinth_incoming_phase_packet_24 m
  · exact generatedNinth_incoming_phase_packet_25 m
  · exact generatedNinth_incoming_phase_packet_26 m
  · exact generatedNinth_incoming_phase_packet_27 m
  · exact generatedNinth_incoming_phase_packet_28 m
  · exact generatedNinth_incoming_phase_packet_29 m
  · exact generatedNinth_incoming_phase_packet_30 m
  · exact generatedNinth_incoming_phase_packet_31 m

/-- Every original incoming odd label retains its exact full source phase certificate. -/
theorem generatedNinth_incoming_phase_certificate (d : Fin 2048) :
    generatedNinthIncomingShortNumerator (generatedNinthIncomingSource d) ≠ 0 →
      Multiplicative.toAdd (generatedNinthQImage
        (generatedNinthIncomingShortQ (generatedNinthIncomingSource d))).coeff =
          generatedNinthIncomingPhase d := by
  let k : Fin 32 := ⟨d.val / 64, by omega⟩
  let m : Fin 64 := ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
  have hd : (⟨64 * k.val + m.val, by omega⟩ : Fin 2048) = d := by
    apply Fin.ext
    dsimp only [k, m]
    omega
  simpa only [hd] using blocks k m

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
