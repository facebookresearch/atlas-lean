/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket16SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket16TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket16VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket16PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket16CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket16KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 16: rows 1024 through 1087; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket16 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 16

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket16SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 16 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_16_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket16SourceMask := by
  exact generatedTenth_root_two_certificates_packet_16_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket16TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 16 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_16_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket16TargetMask := by
  exact generatedTenth_root_two_certificates_packet_16_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket16Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 16 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_16_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket16Vector := by
  exact generatedTenth_root_two_certificates_packet_16_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket16Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 16 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_16_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket16Phase := by
  exact generatedTenth_root_two_certificates_packet_16_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket16Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 16 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_16_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket16Coverage := by
  exact generatedTenth_root_two_certificates_packet_16_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket16Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 16 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_16_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket16Keys := by
  exact generatedTenth_root_two_certificates_packet_16_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_16
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket16SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket16TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket16Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket16Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket16Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket16Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket16 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_16_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket16 := by
  apply generatedTenth_root_two_certificates_packet_16
  · exact generatedTenth_root_two_certificates_packet_16_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_16_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_16_vector_checked
  · exact generatedTenth_root_two_certificates_packet_16_phase_checked
  · exact generatedTenth_root_two_certificates_packet_16_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_16_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
