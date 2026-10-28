/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket05SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket05TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket05VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket05PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket05CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket05KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 05: rows 320 through 383; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket05 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 5

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket05SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 5 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_05_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket05SourceMask := by
  exact generatedTenth_root_two_certificates_packet_05_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket05TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 5 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_05_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket05TargetMask := by
  exact generatedTenth_root_two_certificates_packet_05_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket05Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 5 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_05_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket05Vector := by
  exact generatedTenth_root_two_certificates_packet_05_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket05Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 5 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_05_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket05Phase := by
  exact generatedTenth_root_two_certificates_packet_05_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket05Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 5 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_05_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket05Coverage := by
  exact generatedTenth_root_two_certificates_packet_05_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket05Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 5 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_05_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket05Keys := by
  exact generatedTenth_root_two_certificates_packet_05_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_05
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket05SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket05TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket05Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket05Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket05Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket05Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket05 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_05_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket05 := by
  apply generatedTenth_root_two_certificates_packet_05
  · exact generatedTenth_root_two_certificates_packet_05_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_05_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_05_vector_checked
  · exact generatedTenth_root_two_certificates_packet_05_phase_checked
  · exact generatedTenth_root_two_certificates_packet_05_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_05_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
