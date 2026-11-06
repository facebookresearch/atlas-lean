/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactIncomingPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceInitialTensorSparseActions

/-! Complete actual compact incoming tensor as its 64 original paired source atoms. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000

/-- Every actual compact incoming tensor coordinate is the sum of all original paired atoms. -/
theorem generatedTenth_source_compact_incoming_paired_atoms :
    generatedTenthSourceCompactIncomingPacket.2.2 =
      ∑ p : GeneratedTenthSourceInitialTensorSparseIndex,
        generatedTenthAxisLowerRecoverySourceCompactTensor
          (generatedTenthSourceInitialTensorSparseAtom p) := by
  rw [generatedTenth_source_compact_incoming_packet_tensor,
    generatedTenth_source_initial_tensor_sparse_actual_sum, map_sum]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
