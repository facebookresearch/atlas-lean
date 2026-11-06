/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateCoverageLastPacketGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket64CoverageBlock00Leaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket64CoverageBlock01Leaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket64CoverageBlock02Leaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortPacketRewriteGeneric

/-! Complete original coverage from verified finite blocks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Closed original packet obligation with its full finite index domain. -/
theorem generatedTenth_root_two_certificates_packet_64_coverage_leaf_checked :
  ∀ i : Fin 40, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 64 i) := by
  intro i
  exact generatedTenth_root_two_coverage_last_packet_cover
    (fun k : Fin 40 => GeneratedTenthRootTwoCertificateCoverageCheck
      (generatedTenthRootTwoCertificateRowIndex 64 k))
    (by simpa only [Nat.mul_zero, Nat.zero_add] using
      generatedTenth_root_two_certificates_packet_64_coverage_block_00_checked)
    (by simpa only [Nat.mul_one] using
      generatedTenth_root_two_certificates_packet_64_coverage_block_01_checked)
    generatedTenth_root_two_certificates_packet_64_coverage_block_02_checked
    i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
