/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket01SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket01TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket01VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket01PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket01CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket01KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 01: rows 64 through 127; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket01 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 1

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket01SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 1 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_01_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket01SourceMask := by
  exact generatedTenth_root_two_certificates_packet_01_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket01TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 1 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_01_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket01TargetMask := by
  exact generatedTenth_root_two_certificates_packet_01_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket01Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 1 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_01_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket01Vector := by
  exact generatedTenth_root_two_certificates_packet_01_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket01Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 1 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_01_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket01Phase := by
  exact generatedTenth_root_two_certificates_packet_01_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket01Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 1 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_01_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket01Coverage := by
  exact generatedTenth_root_two_certificates_packet_01_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket01Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 1 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_01_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket01Keys := by
  exact generatedTenth_root_two_certificates_packet_01_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_01
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket01SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket01TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket01Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket01Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket01Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket01Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket01 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_01_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket01 := by
  apply generatedTenth_root_two_certificates_packet_01
  · exact generatedTenth_root_two_certificates_packet_01_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_01_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_01_vector_checked
  · exact generatedTenth_root_two_certificates_packet_01_phase_checked
  · exact generatedTenth_root_two_certificates_packet_01_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_01_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
