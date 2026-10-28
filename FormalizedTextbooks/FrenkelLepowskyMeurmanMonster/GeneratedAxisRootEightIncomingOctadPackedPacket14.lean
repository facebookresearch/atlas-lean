/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingOctadPackedData

/-! One complete original octad-source interval, retaining every signed coefficient and zero. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
-- Check every original source sign in all octads of this complete interval.
/-- The entire packed original octad source agrees with the exact original signed lookup. -/
theorem generatedRootEight_incoming_octad_packed_packet_14 : ∀ u : Fin 16, ∀ f : Fin 64,
    generatedRootEightIncomingOctadPackedCoefficient ⟨224 + u.val, by omega⟩ f =
      generatedFifthRootEightShortCachedCoefficient
        (Sum.inr (Sum.inl (⟨224 + u.val, by omega⟩, f))) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
