/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket26
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket27
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket28
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket29
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket30
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientPacket31

/-! All original incoming odd-column coefficient packets have their exact source meaning. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem blocks (k : Fin 32) (m : Fin 64) :
    let d : Fin 2048 := ⟨64 * k.val + m.val, by omega⟩
    (if generatedNinthIncomingPhase d = 0 then (1 : ℤ) else -1) *
      generatedNinthIncomingShortNumerator (generatedNinthIncomingSource d) =
        generatedNinthIncomingCoefficient d := by
  fin_cases k
  · exact generatedNinth_incoming_coefficient_packet_00 m
  · exact generatedNinth_incoming_coefficient_packet_01 m
  · exact generatedNinth_incoming_coefficient_packet_02 m
  · exact generatedNinth_incoming_coefficient_packet_03 m
  · exact generatedNinth_incoming_coefficient_packet_04 m
  · exact generatedNinth_incoming_coefficient_packet_05 m
  · exact generatedNinth_incoming_coefficient_packet_06 m
  · exact generatedNinth_incoming_coefficient_packet_07 m
  · exact generatedNinth_incoming_coefficient_packet_08 m
  · exact generatedNinth_incoming_coefficient_packet_09 m
  · exact generatedNinth_incoming_coefficient_packet_10 m
  · exact generatedNinth_incoming_coefficient_packet_11 m
  · exact generatedNinth_incoming_coefficient_packet_12 m
  · exact generatedNinth_incoming_coefficient_packet_13 m
  · exact generatedNinth_incoming_coefficient_packet_14 m
  · exact generatedNinth_incoming_coefficient_packet_15 m
  · exact generatedNinth_incoming_coefficient_packet_16 m
  · exact generatedNinth_incoming_coefficient_packet_17 m
  · exact generatedNinth_incoming_coefficient_packet_18 m
  · exact generatedNinth_incoming_coefficient_packet_19 m
  · exact generatedNinth_incoming_coefficient_packet_20 m
  · exact generatedNinth_incoming_coefficient_packet_21 m
  · exact generatedNinth_incoming_coefficient_packet_22 m
  · exact generatedNinth_incoming_coefficient_packet_23 m
  · exact generatedNinth_incoming_coefficient_packet_24 m
  · exact generatedNinth_incoming_coefficient_packet_25 m
  · exact generatedNinth_incoming_coefficient_packet_26 m
  · exact generatedNinth_incoming_coefficient_packet_27 m
  · exact generatedNinth_incoming_coefficient_packet_28 m
  · exact generatedNinth_incoming_coefficient_packet_29 m
  · exact generatedNinth_incoming_coefficient_packet_30 m
  · exact generatedNinth_incoming_coefficient_packet_31 m

/-- Every original incoming odd label retains its exact full source coefficient certificate. -/
theorem generatedNinth_incoming_coefficient_certificate (d : Fin 2048) :
    (if generatedNinthIncomingPhase d = 0 then (1 : ℤ) else -1) *
      generatedNinthIncomingShortNumerator (generatedNinthIncomingSource d) =
        generatedNinthIncomingCoefficient d := by
  let k : Fin 32 := ⟨d.val / 64, by omega⟩
  let m : Fin 64 := ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
  have hd : (⟨64 * k.val + m.val, by omega⟩ : Fin 2048) = d := by
    apply Fin.ext
    dsimp only [k, m]
    omega
  simpa only [hd] using blocks k m

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
