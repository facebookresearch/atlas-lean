/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortJoin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortPacket23

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

private theorem short_fixer_full_packet (g : Fin 4) (k : Fin 23) (u : Fin 4096) :
    generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨4096*k.val+u.val, by omega⟩) := by
  fin_cases k
  · exact generatedRootEight_mathieu_reduced_short_packet_00 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_01 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_02 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_03 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_04 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_05 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_06 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_07 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_08 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_09 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_10 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_11 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_12 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_13 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_14 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_15 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_16 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_17 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_18 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_19 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_20 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_21 g u
  · exact generatedRootEight_mathieu_reduced_short_packet_22 g u

private theorem short_fixer_all_addresses (g : Fin 4) (n : Fin 98280) :
    generatedRootEightMathieuReducedShortSupportCondition g (generatedNinthLowerSpinShortIndex n) :=
  generatedRootEight_mathieu_reduced_short_join
    (fun g n => generatedRootEightMathieuReducedShortSupportCondition g (generatedNinthLowerSpinShortIndex n))
    (fun k g u => short_fixer_full_packet g k u)
    (fun g u => generatedRootEight_mathieu_reduced_short_packet_23 g u) g n

/-- Every nonzero original coordinate has its complete Q phase and fixed signed coefficient. -/
theorem generatedRootEight_mathieu_reduced_short_certificate (g : Fin 4) (r : GriessShortIndex) :
    generatedRootEightMathieuReducedShortSupportCondition g r := by
  simpa only [generatedNinth_lower_spin_short_index_address] using
    short_fixer_all_addresses g (generatedNinthLowerSpinShortAddress r)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
