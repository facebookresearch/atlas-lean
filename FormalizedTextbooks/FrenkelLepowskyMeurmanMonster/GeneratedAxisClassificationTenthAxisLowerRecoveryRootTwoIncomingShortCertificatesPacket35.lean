/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket35SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket35TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket35VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket35PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket35CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket35KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 35: rows 2240 through 2303; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket35 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 35

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket35SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 35 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_35_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket35SourceMask := by
  exact generatedTenth_root_two_certificates_packet_35_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket35TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 35 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_35_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket35TargetMask := by
  exact generatedTenth_root_two_certificates_packet_35_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket35Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 35 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_35_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket35Vector := by
  exact generatedTenth_root_two_certificates_packet_35_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket35Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 35 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_35_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket35Phase := by
  exact generatedTenth_root_two_certificates_packet_35_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket35Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 35 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_35_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket35Coverage := by
  exact generatedTenth_root_two_certificates_packet_35_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket35Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 35 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_35_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket35Keys := by
  exact generatedTenth_root_two_certificates_packet_35_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_35
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket35SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket35TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket35Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket35Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket35Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket35Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket35 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_35_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket35 := by
  apply generatedTenth_root_two_certificates_packet_35
  · exact generatedTenth_root_two_certificates_packet_35_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_35_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_35_vector_checked
  · exact generatedTenth_root_two_certificates_packet_35_phase_checked
  · exact generatedTenth_root_two_certificates_packet_35_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_35_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
