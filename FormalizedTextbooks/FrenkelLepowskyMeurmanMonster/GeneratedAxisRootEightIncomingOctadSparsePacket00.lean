/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingOctadSparseSum

/-! Complete signed coefficient binding for a disjoint original octad interval. -/
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- Every original slot in this full interval equals the sparse list coefficient. -/
theorem generatedRootEight_incoming_octad_sparse_packet_00 :
    ∀ u : Fin 253, ∀ f : Fin 64,
    generatedRootEightSparseCoefficient
      (generatedRootEightIncomingOctadSparseEntries ⟨0 + u.val, by omega⟩) f =
      generatedRootEightIncomingOctadPackedCoefficient ⟨0 + u.val, by omega⟩ f := by
  unfold generatedRootEightSparseCoefficient generatedRootEightIncomingOctadSparseEntries
    generatedRootEightIncomingOctadSparseWords generatedRootEightIncomingOctadPackedCoefficient
    generatedRootEightIncomingOctadPositiveTwoWords
    generatedRootEightIncomingOctadNegativeTwoWords
    generatedRootEightIncomingOctadPositiveFourWords
    generatedRootEightIncomingOctadNegativeFourWords
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
