/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortPacketRewriteGeneric

/-! Independent finite proof draft. This module has not been compiled. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Closed original packet obligation with its full finite index domain. -/
theorem generatedTenth_root_two_certificates_packet_16_phase_leaf_checked :
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 16 i) := by
  unfold GeneratedTenthRootTwoCertificatePhaseCheck
  simp_rw [← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
