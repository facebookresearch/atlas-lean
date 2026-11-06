/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket24SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket24TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket24VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket24PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket24CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket24KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 24: rows 1536 through 1599; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket24 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 24

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket24SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 24 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_24_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket24SourceMask := by
  exact generatedTenth_root_two_certificates_packet_24_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket24TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 24 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_24_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket24TargetMask := by
  exact generatedTenth_root_two_certificates_packet_24_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket24Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 24 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_24_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket24Vector := by
  exact generatedTenth_root_two_certificates_packet_24_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket24Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 24 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_24_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket24Phase := by
  exact generatedTenth_root_two_certificates_packet_24_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket24Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 24 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_24_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket24Coverage := by
  exact generatedTenth_root_two_certificates_packet_24_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket24Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 24 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_24_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket24Keys := by
  exact generatedTenth_root_two_certificates_packet_24_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_24
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket24SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket24TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket24Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket24Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket24Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket24Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket24 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_24_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket24 := by
  apply generatedTenth_root_two_certificates_packet_24
  · exact generatedTenth_root_two_certificates_packet_24_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_24_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_24_vector_checked
  · exact generatedTenth_root_two_certificates_packet_24_phase_checked
  · exact generatedTenth_root_two_certificates_packet_24_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_24_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
