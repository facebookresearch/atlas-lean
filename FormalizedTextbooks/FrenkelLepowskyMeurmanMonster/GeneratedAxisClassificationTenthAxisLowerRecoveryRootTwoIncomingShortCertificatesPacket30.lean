/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket30SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket30TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket30VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket30PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket30CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket30KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 30: rows 1920 through 1983; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket30 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 30

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket30SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 30 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_30_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket30SourceMask := by
  exact generatedTenth_root_two_certificates_packet_30_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket30TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 30 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_30_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket30TargetMask := by
  exact generatedTenth_root_two_certificates_packet_30_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket30Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 30 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_30_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket30Vector := by
  exact generatedTenth_root_two_certificates_packet_30_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket30Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 30 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_30_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket30Phase := by
  exact generatedTenth_root_two_certificates_packet_30_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket30Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 30 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_30_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket30Coverage := by
  exact generatedTenth_root_two_certificates_packet_30_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket30Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 30 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_30_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket30Keys := by
  exact generatedTenth_root_two_certificates_packet_30_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_30
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket30SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket30TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket30Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket30Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket30Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket30Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket30 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_30_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket30 := by
  apply generatedTenth_root_two_certificates_packet_30
  · exact generatedTenth_root_two_certificates_packet_30_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_30_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_30_vector_checked
  · exact generatedTenth_root_two_certificates_packet_30_phase_checked
  · exact generatedTenth_root_two_certificates_packet_30_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_30_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
