/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerCSupportCertificateGeneric

/-! Ungated exact candidate support data/certificates; numerical parsing is not proof. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 8000000 in
-- Scope full preferred masks, original central phase, and signed C to this packet.
/-- Every retained nonzero source has its exact full signed preferred-Q image. -/
theorem generatedTenth_two_fixer_c_support_row_01_103 :
    ∀ u : Fin 256, GeneratedTenthTwoFixerCSupportRowCertificate 1
      (generatedTenthTwoFixerCSupportRowLabel 103 u) := by
  unfold GeneratedTenthTwoFixerCSupportRowCertificate
    GeneratedTenthTwoFixerCPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
