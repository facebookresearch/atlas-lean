/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket29SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket29TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket29VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket29PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket29CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket29KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 29: rows 1856 through 1919; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket29 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 29

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket29SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 29 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_29_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket29SourceMask := by
  exact generatedTenth_root_two_certificates_packet_29_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket29TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 29 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_29_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket29TargetMask := by
  exact generatedTenth_root_two_certificates_packet_29_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket29Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 29 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_29_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket29Vector := by
  exact generatedTenth_root_two_certificates_packet_29_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket29Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 29 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_29_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket29Phase := by
  exact generatedTenth_root_two_certificates_packet_29_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket29Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 29 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_29_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket29Coverage := by
  exact generatedTenth_root_two_certificates_packet_29_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket29Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 29 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_29_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket29Keys := by
  exact generatedTenth_root_two_certificates_packet_29_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_29
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket29SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket29TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket29Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket29Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket29Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket29Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket29 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_29_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket29 := by
  apply generatedTenth_root_two_certificates_packet_29
  · exact generatedTenth_root_two_certificates_packet_29_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_29_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_29_vector_checked
  · exact generatedTenth_root_two_certificates_packet_29_phase_checked
  · exact generatedTenth_root_two_certificates_packet_29_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_29_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
