/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket14SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket14TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket14VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket14PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket14CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket14KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 14: rows 896 through 959; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket14 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 14

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket14SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 14 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_14_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket14SourceMask := by
  exact generatedTenth_root_two_certificates_packet_14_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket14TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 14 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_14_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket14TargetMask := by
  exact generatedTenth_root_two_certificates_packet_14_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket14Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 14 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_14_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket14Vector := by
  exact generatedTenth_root_two_certificates_packet_14_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket14Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 14 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_14_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket14Phase := by
  exact generatedTenth_root_two_certificates_packet_14_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket14Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 14 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_14_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket14Coverage := by
  exact generatedTenth_root_two_certificates_packet_14_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket14Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 14 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_14_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket14Keys := by
  exact generatedTenth_root_two_certificates_packet_14_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_14
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket14SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket14TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket14Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket14Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket14Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket14Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket14 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_14_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket14 := by
  apply generatedTenth_root_two_certificates_packet_14
  · exact generatedTenth_root_two_certificates_packet_14_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_14_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_14_vector_checked
  · exact generatedTenth_root_two_certificates_packet_14_phase_checked
  · exact generatedTenth_root_two_certificates_packet_14_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_14_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
