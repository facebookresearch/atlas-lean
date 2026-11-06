/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortPacketRewriteGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoCoverageArrayRewriteGeneric

/-! Exact finite coverage split. All new proof bodies are uncompiled drafts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Every original coverage check in this block, including all zero rows. -/
theorem generatedTenth_root_two_certificates_packet_13_coverage_block_01_checked :
    ∀ u : Fin 16, GeneratedTenthRootTwoCertificateCoverageCheck
      (generatedTenthRootTwoCertificateRowIndex 13 ⟨16 * 1 + u.val, by omega⟩) := by
  unfold GeneratedTenthRootTwoCertificateCoverageCheck
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryKey
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryNumerator
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTarget
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTargetAddress
    generatedTenthRootTwoCertificateSignedNumerator
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowPhase
  simp_rw [←generatedTenth_root_two_coverage_dictionary_word_cached_actual,
    ←generatedTenth_root_two_coverage_row_descriptor_cached_actual]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
