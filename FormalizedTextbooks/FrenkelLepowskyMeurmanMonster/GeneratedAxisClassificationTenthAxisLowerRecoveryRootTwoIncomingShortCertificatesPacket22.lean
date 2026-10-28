/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket22SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket22TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket22VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket22PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket22CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket22KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 22: rows 1408 through 1471; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket22 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 22

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket22SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 22 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_22_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket22SourceMask := by
  exact generatedTenth_root_two_certificates_packet_22_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket22TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 22 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_22_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket22TargetMask := by
  exact generatedTenth_root_two_certificates_packet_22_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket22Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 22 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_22_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket22Vector := by
  exact generatedTenth_root_two_certificates_packet_22_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket22Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 22 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_22_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket22Phase := by
  exact generatedTenth_root_two_certificates_packet_22_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket22Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 22 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_22_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket22Coverage := by
  exact generatedTenth_root_two_certificates_packet_22_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket22Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 22 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_22_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket22Keys := by
  exact generatedTenth_root_two_certificates_packet_22_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_22
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket22SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket22TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket22Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket22Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket22Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket22Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket22 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_22_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket22 := by
  apply generatedTenth_root_two_certificates_packet_22
  · exact generatedTenth_root_two_certificates_packet_22_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_22_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_22_vector_checked
  · exact generatedTenth_root_two_certificates_packet_22_phase_checked
  · exact generatedTenth_root_two_certificates_packet_22_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_22_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
