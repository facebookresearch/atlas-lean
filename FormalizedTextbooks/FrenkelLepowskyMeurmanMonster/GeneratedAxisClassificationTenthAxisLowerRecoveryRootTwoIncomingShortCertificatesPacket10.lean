/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket10SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket10TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket10VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket10PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket10CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket10KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 10: rows 640 through 703; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket10 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 10

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket10SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 10 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_10_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket10SourceMask := by
  exact generatedTenth_root_two_certificates_packet_10_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket10TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 10 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_10_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket10TargetMask := by
  exact generatedTenth_root_two_certificates_packet_10_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket10Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 10 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_10_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket10Vector := by
  exact generatedTenth_root_two_certificates_packet_10_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket10Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 10 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_10_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket10Phase := by
  exact generatedTenth_root_two_certificates_packet_10_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket10Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 10 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_10_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket10Coverage := by
  exact generatedTenth_root_two_certificates_packet_10_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket10Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 10 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_10_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket10Keys := by
  exact generatedTenth_root_two_certificates_packet_10_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_10
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket10SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket10TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket10Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket10Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket10Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket10Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket10 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_10_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket10 := by
  apply generatedTenth_root_two_certificates_packet_10
  · exact generatedTenth_root_two_certificates_packet_10_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_10_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_10_vector_checked
  · exact generatedTenth_root_two_certificates_packet_10_phase_checked
  · exact generatedTenth_root_two_certificates_packet_10_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_10_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
