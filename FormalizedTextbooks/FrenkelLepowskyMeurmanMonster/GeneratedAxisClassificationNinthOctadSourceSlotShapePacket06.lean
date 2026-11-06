/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotFourierData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacketCover

/-! Exact original slot-label XOR and signed-numerator conditions for the sparse octad
source shapes. All actual source-word certificates are separate prerequisites. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 40000000 in
-- Check the original source shape at the next8 octad addresses.
private theorem slot_shape_06_0 : ∀ m : Fin 8,
    let o := generatedNinthOctadPacketIndex (⟨6, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨0, by decide⟩ : Fin 8) m)
    o = 459 ∨ GeneratedNinthOctadTwoSlotShape o ∨ GeneratedNinthOctadFourSlotShape o := by
  unfold GeneratedNinthOctadTwoSlotShape GeneratedNinthOctadFourSlotShape
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check the original source shape at the next8 octad addresses.
private theorem slot_shape_06_1 : ∀ m : Fin 8,
    let o := generatedNinthOctadPacketIndex (⟨6, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨1, by decide⟩ : Fin 8) m)
    o = 459 ∨ GeneratedNinthOctadTwoSlotShape o ∨ GeneratedNinthOctadFourSlotShape o := by
  unfold GeneratedNinthOctadTwoSlotShape GeneratedNinthOctadFourSlotShape
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check the original source shape at the next8 octad addresses.
private theorem slot_shape_06_2 : ∀ m : Fin 8,
    let o := generatedNinthOctadPacketIndex (⟨6, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨2, by decide⟩ : Fin 8) m)
    o = 459 ∨ GeneratedNinthOctadTwoSlotShape o ∨ GeneratedNinthOctadFourSlotShape o := by
  unfold GeneratedNinthOctadTwoSlotShape GeneratedNinthOctadFourSlotShape
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check the original source shape at the next8 octad addresses.
private theorem slot_shape_06_3 : ∀ m : Fin 8,
    let o := generatedNinthOctadPacketIndex (⟨6, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨3, by decide⟩ : Fin 8) m)
    o = 459 ∨ GeneratedNinthOctadTwoSlotShape o ∨ GeneratedNinthOctadFourSlotShape o := by
  unfold GeneratedNinthOctadTwoSlotShape GeneratedNinthOctadFourSlotShape
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check the original source shape at the next8 octad addresses.
private theorem slot_shape_06_4 : ∀ m : Fin 8,
    let o := generatedNinthOctadPacketIndex (⟨6, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨4, by decide⟩ : Fin 8) m)
    o = 459 ∨ GeneratedNinthOctadTwoSlotShape o ∨ GeneratedNinthOctadFourSlotShape o := by
  unfold GeneratedNinthOctadTwoSlotShape GeneratedNinthOctadFourSlotShape
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check the original source shape at the next8 octad addresses.
private theorem slot_shape_06_5 : ∀ m : Fin 8,
    let o := generatedNinthOctadPacketIndex (⟨6, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨5, by decide⟩ : Fin 8) m)
    o = 459 ∨ GeneratedNinthOctadTwoSlotShape o ∨ GeneratedNinthOctadFourSlotShape o := by
  unfold GeneratedNinthOctadTwoSlotShape GeneratedNinthOctadFourSlotShape
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check the original source shape at the next8 octad addresses.
private theorem slot_shape_06_6 : ∀ m : Fin 8,
    let o := generatedNinthOctadPacketIndex (⟨6, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨6, by decide⟩ : Fin 8) m)
    o = 459 ∨ GeneratedNinthOctadTwoSlotShape o ∨ GeneratedNinthOctadFourSlotShape o := by
  unfold GeneratedNinthOctadTwoSlotShape GeneratedNinthOctadFourSlotShape
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check the original source shape at the next8 octad addresses.
private theorem slot_shape_06_7 : ∀ m : Fin 8,
    let o := generatedNinthOctadPacketIndex (⟨6, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨7, by decide⟩ : Fin 8) m)
    o = 459 ∨ GeneratedNinthOctadTwoSlotShape o ∨ GeneratedNinthOctadFourSlotShape o := by
  unfold GeneratedNinthOctadTwoSlotShape GeneratedNinthOctadFourSlotShape
  decide +kernel

/-- Every octad in packet06 has the original two/four slot shape or is octad459. -/
theorem generatedNinth_octad_source_shape_packet_06 : ∀ m : Fin 64,
    let o := generatedNinthOctadPacketIndex (⟨6, by decide⟩ : Fin 12) m
    o = 459 ∨ GeneratedNinthOctadTwoSlotShape o ∨ GeneratedNinthOctadFourSlotShape o := by
  apply generatedNinth_slot_subpacket_cover_64
  intro b
  fin_cases b
  · exact slot_shape_06_0
  · exact slot_shape_06_1
  · exact slot_shape_06_2
  · exact slot_shape_06_3
  · exact slot_shape_06_4
  · exact slot_shape_06_5
  · exact slot_shape_06_6
  · exact slot_shape_06_7

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
