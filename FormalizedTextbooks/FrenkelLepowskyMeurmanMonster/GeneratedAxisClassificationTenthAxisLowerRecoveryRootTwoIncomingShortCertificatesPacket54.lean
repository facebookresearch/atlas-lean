/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket54SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket54TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket54VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket54PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket54CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket54KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 54: rows 3456 through 3519; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket54 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 54

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket54SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 54 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_54_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket54SourceMask := by
  exact generatedTenth_root_two_certificates_packet_54_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket54TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 54 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_54_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket54TargetMask := by
  exact generatedTenth_root_two_certificates_packet_54_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket54Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 54 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_54_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket54Vector := by
  exact generatedTenth_root_two_certificates_packet_54_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket54Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 54 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_54_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket54Phase := by
  exact generatedTenth_root_two_certificates_packet_54_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket54Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 54 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_54_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket54Coverage := by
  exact generatedTenth_root_two_certificates_packet_54_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket54Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 54 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_54_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket54Keys := by
  exact generatedTenth_root_two_certificates_packet_54_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_54
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket54SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket54TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket54Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket54Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket54Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket54Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket54 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_54_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket54 := by
  apply generatedTenth_root_two_certificates_packet_54
  · exact generatedTenth_root_two_certificates_packet_54_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_54_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_54_vector_checked
  · exact generatedTenth_root_two_certificates_packet_54_phase_checked
  · exact generatedTenth_root_two_certificates_packet_54_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_54_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
