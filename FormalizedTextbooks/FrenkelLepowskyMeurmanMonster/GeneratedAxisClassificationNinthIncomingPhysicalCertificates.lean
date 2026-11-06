/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket26
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket27
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket28
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket29
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket30
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalPacket31

/-! All original incoming odd-column physical packets have their exact source meaning. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem blocks (k : Fin 32) (m : Fin 64) (i : Fin 24) :
    let d : Fin 2048 := ⟨64 * k.val + m.val, by omega⟩
    (∑ j : Fin 24, generatedNinthInverseNumerator i j *
      ((if (golayEncodedMask d.val).testBit j.val then (-1 : ℤ) else 1) *
        (if j = 1 then -3 else 1))) =
      8 * generatedNinthIncomingPhysicalSign d *
        generatedNinthIncomingShortIntegral (generatedNinthIncomingSource d) i := by
  fin_cases k
  · exact generatedNinth_incoming_physical_packet_00 m i
  · exact generatedNinth_incoming_physical_packet_01 m i
  · exact generatedNinth_incoming_physical_packet_02 m i
  · exact generatedNinth_incoming_physical_packet_03 m i
  · exact generatedNinth_incoming_physical_packet_04 m i
  · exact generatedNinth_incoming_physical_packet_05 m i
  · exact generatedNinth_incoming_physical_packet_06 m i
  · exact generatedNinth_incoming_physical_packet_07 m i
  · exact generatedNinth_incoming_physical_packet_08 m i
  · exact generatedNinth_incoming_physical_packet_09 m i
  · exact generatedNinth_incoming_physical_packet_10 m i
  · exact generatedNinth_incoming_physical_packet_11 m i
  · exact generatedNinth_incoming_physical_packet_12 m i
  · exact generatedNinth_incoming_physical_packet_13 m i
  · exact generatedNinth_incoming_physical_packet_14 m i
  · exact generatedNinth_incoming_physical_packet_15 m i
  · exact generatedNinth_incoming_physical_packet_16 m i
  · exact generatedNinth_incoming_physical_packet_17 m i
  · exact generatedNinth_incoming_physical_packet_18 m i
  · exact generatedNinth_incoming_physical_packet_19 m i
  · exact generatedNinth_incoming_physical_packet_20 m i
  · exact generatedNinth_incoming_physical_packet_21 m i
  · exact generatedNinth_incoming_physical_packet_22 m i
  · exact generatedNinth_incoming_physical_packet_23 m i
  · exact generatedNinth_incoming_physical_packet_24 m i
  · exact generatedNinth_incoming_physical_packet_25 m i
  · exact generatedNinth_incoming_physical_packet_26 m i
  · exact generatedNinth_incoming_physical_packet_27 m i
  · exact generatedNinth_incoming_physical_packet_28 m i
  · exact generatedNinth_incoming_physical_packet_29 m i
  · exact generatedNinth_incoming_physical_packet_30 m i
  · exact generatedNinth_incoming_physical_packet_31 m i

/-- Every original incoming odd label retains its exact full source physical certificate. -/
theorem generatedNinth_incoming_physical_certificate (d : Fin 2048) (i : Fin 24) :
    (∑ j : Fin 24, generatedNinthInverseNumerator i j *
      ((if (golayEncodedMask d.val).testBit j.val then (-1 : ℤ) else 1) *
        (if j = 1 then -3 else 1))) =
      8 * generatedNinthIncomingPhysicalSign d *
        generatedNinthIncomingShortIntegral (generatedNinthIncomingSource d) i := by
  let k : Fin 32 := ⟨d.val / 64, by omega⟩
  let m : Fin 64 := ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
  have hd : (⟨64 * k.val + m.val, by omega⟩ : Fin 2048) = d := by
    apply Fin.ext
    dsimp only [k, m]
    omega
  have hdv : 64 * k.val + m.val = d.val := by
    dsimp only [k, m]
    omega
  simpa only [hd, hdv] using blocks k m i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
