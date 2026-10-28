/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortSupportActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortBalancedMask
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinParityCircuit

/-! Complete finite preferred-short support transport with its actual central phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
-- Check every original address in this entire finite interval, with all source zeros retained.
/-- Every nonzero original source in this interval has its actual signed canonical image. -/
theorem generatedRootEight_canonical_short_support_packet_54_block_00 :
    ∀ u : Fin 256, generatedRootEightCanonicalShortSupportCondition
      (generatedNinthLowerSpinShortIndex ⟨55296 + u.val, by omega⟩) := by
  unfold generatedRootEightCanonicalShortSupportCondition
    generatedRootEightCanonicalShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
