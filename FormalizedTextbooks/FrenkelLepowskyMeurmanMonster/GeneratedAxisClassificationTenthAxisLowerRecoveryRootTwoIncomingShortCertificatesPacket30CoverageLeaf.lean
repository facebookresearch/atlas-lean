/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateCoverageQuarterGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket30CoverageBlock00Leaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket30CoverageBlock01Leaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket30CoverageBlock02Leaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket30CoverageBlock03Leaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortPacketRewriteGeneric

/-! Complete original coverage from verified finite blocks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Closed original packet obligation with its full finite index domain. -/
theorem generatedTenth_root_two_certificates_packet_30_coverage_leaf_checked :
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 30 i) := by
  intro i
  have h : ∀ b : Fin 4, ∀ u : Fin 16, GeneratedTenthRootTwoCertificateCoverageCheck
      (generatedTenthRootTwoCertificateRowIndex 30 ⟨16 * b.val + u.val, by omega⟩) := by
    intro b
    fin_cases b
    · exact generatedTenth_root_two_certificates_packet_30_coverage_block_00_checked
    · exact generatedTenth_root_two_certificates_packet_30_coverage_block_01_checked
    · exact generatedTenth_root_two_certificates_packet_30_coverage_block_02_checked
    · exact generatedTenth_root_two_certificates_packet_30_coverage_block_03_checked
  exact generatedTenth_root_two_coverage_quarter_cover
    (fun k : Fin 64 => GeneratedTenthRootTwoCertificateCoverageCheck
      (generatedTenthRootTwoCertificateRowIndex 30 k)) h i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
