/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortSupportData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortBalancedMask
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinParityCircuit

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortBoundedQuantifier

/-! Exact full preferred-short Q images and signed coefficients on every nonzero source
in a bounded original row packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
/-- Every nonzero source in this complete bounded original row has its full signed Q image. -/
theorem generatedNinth_lower_spin_short_support_packet_10_part_08_block_00 : ∀ u : Fin 1024,
    if h : 8 * 8192 + 0 * 1024 + u.val < 98280 then
      generatedNinthLowerSpinShortSupportCondition 10
        ⟨8 * 8192 + 0 * 1024 + u.val, h⟩ else True := by
  apply generatedNinth_lower_spin_short_predicate1024_of_blocks
  unfold generatedNinthLowerSpinShortSupportCondition
    generatedNinthLowerSpinShortPackedCondition
  dsimp only [generatedNinthLowerSpinShortPackedColumns,
    generatedNinthLowerSpinShortPackedRows, generatedNinthLowerSpinShortPackedCoefficients]
  simp_rw [← generatedNinth_lower_spin_circuit_q_mask_central,
    ← generatedNinth_lower_spin_short_balanced_mask_actual]
  decide +kernel


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
