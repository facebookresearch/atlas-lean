/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket12SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket12TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket12VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket12PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket12CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket12KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 12: rows 768 through 831; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket12 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 12

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket12SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 12 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_12_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket12SourceMask := by
  exact generatedTenth_root_two_certificates_packet_12_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket12TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 12 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_12_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket12TargetMask := by
  exact generatedTenth_root_two_certificates_packet_12_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket12Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 12 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_12_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket12Vector := by
  exact generatedTenth_root_two_certificates_packet_12_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket12Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 12 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_12_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket12Phase := by
  exact generatedTenth_root_two_certificates_packet_12_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket12Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 12 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_12_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket12Coverage := by
  exact generatedTenth_root_two_certificates_packet_12_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket12Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 12 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_12_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket12Keys := by
  exact generatedTenth_root_two_certificates_packet_12_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_12
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket12SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket12TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket12Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket12Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket12Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket12Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket12 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_12_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket12 := by
  apply generatedTenth_root_two_certificates_packet_12
  · exact generatedTenth_root_two_certificates_packet_12_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_12_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_12_vector_checked
  · exact generatedTenth_root_two_certificates_packet_12_phase_checked
  · exact generatedTenth_root_two_certificates_packet_12_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_12_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
