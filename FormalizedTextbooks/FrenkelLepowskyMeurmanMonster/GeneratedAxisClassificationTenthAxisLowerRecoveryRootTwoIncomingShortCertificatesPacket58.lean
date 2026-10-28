/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket58SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket58TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket58VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket58PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket58CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket58KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 58: rows 3712 through 3775; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket58 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 58

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket58SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 58 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_58_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket58SourceMask := by
  exact generatedTenth_root_two_certificates_packet_58_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket58TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 58 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_58_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket58TargetMask := by
  exact generatedTenth_root_two_certificates_packet_58_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket58Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 58 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_58_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket58Vector := by
  exact generatedTenth_root_two_certificates_packet_58_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket58Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 58 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_58_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket58Phase := by
  exact generatedTenth_root_two_certificates_packet_58_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket58Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 58 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_58_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket58Coverage := by
  exact generatedTenth_root_two_certificates_packet_58_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket58Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 58 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_58_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket58Keys := by
  exact generatedTenth_root_two_certificates_packet_58_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_58
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket58SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket58TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket58Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket58Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket58Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket58Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket58 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_58_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket58 := by
  apply generatedTenth_root_two_certificates_packet_58
  · exact generatedTenth_root_two_certificates_packet_58_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_58_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_58_vector_checked
  · exact generatedTenth_root_two_certificates_packet_58_phase_checked
  · exact generatedTenth_root_two_certificates_packet_58_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_58_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
