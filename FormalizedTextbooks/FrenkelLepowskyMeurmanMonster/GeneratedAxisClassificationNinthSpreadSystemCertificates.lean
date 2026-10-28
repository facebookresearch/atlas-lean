/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket17

/-! Compact source-system equations identify genuine whole-subspace actions of the original
eighteen section letters. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Every compact action equation refers to the original literal section letter. -/
theorem generatedNinth_spread_system_label_image (g : Fin 18) (k : Fin 270) (j : Fin 4) :
    sixthFrameOrbitMaskApply (generatedNinthSpreadColumns g)
      (generatedAxisE8FrameSystemBasisLabels k j).val =
        (generatedAxisE8FrameSystemCandidateLabel (generatedNinthSpreadSystemTarget g k)
          (generatedNinthSpreadSystemCoefficient g k j)).val := by
  fin_cases g
  · exact generatedNinth_spread_system_packet_00 k j
  · exact generatedNinth_spread_system_packet_01 k j
  · exact generatedNinth_spread_system_packet_02 k j
  · exact generatedNinth_spread_system_packet_03 k j
  · exact generatedNinth_spread_system_packet_04 k j
  · exact generatedNinth_spread_system_packet_05 k j
  · exact generatedNinth_spread_system_packet_06 k j
  · exact generatedNinth_spread_system_packet_07 k j
  · exact generatedNinth_spread_system_packet_08 k j
  · exact generatedNinth_spread_system_packet_09 k j
  · exact generatedNinth_spread_system_packet_10 k j
  · exact generatedNinth_spread_system_packet_11 k j
  · exact generatedNinth_spread_system_packet_12 k j
  · exact generatedNinth_spread_system_packet_13 k j
  · exact generatedNinth_spread_system_packet_14 k j
  · exact generatedNinth_spread_system_packet_15 k j
  · exact generatedNinth_spread_system_packet_16 k j
  · exact generatedNinth_spread_system_packet_17 k j

/-- Compact source equations give the exact original binary action on every system basis. -/
theorem generatedNinth_spread_system_basis_image (g : Fin 18) (k : Fin 270) (j : Fin 4) :
    generatedFifthSectionGeneratorBinary g *ᵥ generatedAxisE8FrameSystemCandidateBasis k j =
      generatedAxisE8FrameSystemCandidateMap (generatedNinthSpreadSystemTarget g k)
        (generatedNinthSpreadSystemCoefficient g k j) := by
  exact generatedNinth_spread_system_basis_of_label g k j
    (generatedNinth_spread_system_label_image g k j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
