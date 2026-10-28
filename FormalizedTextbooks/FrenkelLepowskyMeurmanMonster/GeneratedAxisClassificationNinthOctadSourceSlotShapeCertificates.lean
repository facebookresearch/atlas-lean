/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotShapePacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotShapePacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotShapePacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotShapePacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotShapePacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotShapePacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotShapePacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotShapePacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotShapePacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotShapePacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotShapePacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotShapePacket11

/-! Complete finite packet coverage gives the original two/four-term source shape at every
nonexceptional octad. Actual source coefficients and full phases are separate certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every original octad source block has the checked sparse shape, except octad459. -/
theorem generatedNinth_octad_source_shape (o : Fin 759) :
    o = 459 ∨ GeneratedNinthOctadTwoSlotShape o ∨ GeneratedNinthOctadFourSlotShape o := by
  have h : ∀ o : Fin 759,
      o = 459 ∨ GeneratedNinthOctadTwoSlotShape o ∨ GeneratedNinthOctadFourSlotShape o := by
    apply generatedNinth_octad_packet_cover
    intro b
    fin_cases b
    · exact generatedNinth_octad_source_shape_packet_00
    · exact generatedNinth_octad_source_shape_packet_01
    · exact generatedNinth_octad_source_shape_packet_02
    · exact generatedNinth_octad_source_shape_packet_03
    · exact generatedNinth_octad_source_shape_packet_04
    · exact generatedNinth_octad_source_shape_packet_05
    · exact generatedNinth_octad_source_shape_packet_06
    · exact generatedNinth_octad_source_shape_packet_07
    · exact generatedNinth_octad_source_shape_packet_08
    · exact generatedNinth_octad_source_shape_packet_09
    · exact generatedNinth_octad_source_shape_packet_10
    · exact generatedNinth_octad_source_shape_packet_11
  exact h o

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
