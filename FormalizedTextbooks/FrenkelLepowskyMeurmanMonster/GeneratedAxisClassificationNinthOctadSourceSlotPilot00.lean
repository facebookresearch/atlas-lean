/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotPacketCover

/-! Finite original descriptor and source-address checks on one consecutive packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
/-- Nonempty slots in octad packet00 have their original source and target descriptors. -/
theorem generatedNinth_octad_slot_target_pilot_target_00 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨0, by decide⟩ : Fin 12) (⟨m.val, by omega⟩ : Fin 64)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
