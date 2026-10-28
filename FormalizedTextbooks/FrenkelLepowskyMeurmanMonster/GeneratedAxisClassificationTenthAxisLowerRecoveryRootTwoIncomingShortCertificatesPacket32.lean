/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket32SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket32TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket32VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket32PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket32CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket32KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 32: rows 2048 through 2111; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket32 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 32

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket32SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 32 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_32_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket32SourceMask := by
  exact generatedTenth_root_two_certificates_packet_32_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket32TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 32 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_32_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket32TargetMask := by
  exact generatedTenth_root_two_certificates_packet_32_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket32Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 32 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_32_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket32Vector := by
  exact generatedTenth_root_two_certificates_packet_32_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket32Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 32 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_32_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket32Phase := by
  exact generatedTenth_root_two_certificates_packet_32_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket32Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 32 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_32_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket32Coverage := by
  exact generatedTenth_root_two_certificates_packet_32_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket32Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 32 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_32_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket32Keys := by
  exact generatedTenth_root_two_certificates_packet_32_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_32
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket32SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket32TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket32Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket32Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket32Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket32Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket32 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_32_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket32 := by
  apply generatedTenth_root_two_certificates_packet_32
  · exact generatedTenth_root_two_certificates_packet_32_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_32_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_32_vector_checked
  · exact generatedTenth_root_two_certificates_packet_32_phase_checked
  · exact generatedTenth_root_two_certificates_packet_32_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_32_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
