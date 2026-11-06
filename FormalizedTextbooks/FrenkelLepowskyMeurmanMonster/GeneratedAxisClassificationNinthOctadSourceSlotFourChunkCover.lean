/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacketCover

/-! Four-address intervals cover the original eight-address and final seven-address
source subpackets. This index cover does not assert any source or target relation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A four-address interval inside the original eight-address subpacket. -/
def generatedNinthSlotFourChunkIndex8 (h : Fin 2) (m : Fin 4) : Fin 8 :=
  Fin.ofNat 8 (4 * h.val + m.val)

/-- A four-address interval in the final seven-address subpacket, with one repeated address. -/
def generatedNinthSlotFourChunkIndex7 (h : Fin 2) (m : Fin 4) : Fin 7 :=
  Fin.ofNat 7 (4 * h.val + m.val)

/-- The two four-address intervals cover all eight original addresses exactly as indices. -/
theorem generatedNinth_slot_four_chunk_cover8 : ∀ m : Fin 8,
    ∃ (h : Fin 2) (n : Fin 4), generatedNinthSlotFourChunkIndex8 h n = m := by
  decide +kernel

/-- The final two intervals cover all seven original addresses exactly as indices. -/
theorem generatedNinth_slot_four_chunk_cover7 : ∀ m : Fin 7,
    ∃ (h : Fin 2) (n : Fin 4), generatedNinthSlotFourChunkIndex7 h n = m := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
