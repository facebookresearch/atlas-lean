/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket57SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket57TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket57VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket57PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket57CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket57KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 57: rows 3648 through 3711; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket57 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 57

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket57SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 57 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_57_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket57SourceMask := by
  exact generatedTenth_root_two_certificates_packet_57_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket57TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 57 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_57_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket57TargetMask := by
  exact generatedTenth_root_two_certificates_packet_57_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket57Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 57 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_57_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket57Vector := by
  exact generatedTenth_root_two_certificates_packet_57_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket57Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 57 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_57_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket57Phase := by
  exact generatedTenth_root_two_certificates_packet_57_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket57Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 57 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_57_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket57Coverage := by
  exact generatedTenth_root_two_certificates_packet_57_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket57Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 57 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_57_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket57Keys := by
  exact generatedTenth_root_two_certificates_packet_57_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_57
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket57SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket57TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket57Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket57Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket57Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket57Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket57 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_57_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket57 := by
  apply generatedTenth_root_two_certificates_packet_57
  · exact generatedTenth_root_two_certificates_packet_57_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_57_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_57_vector_checked
  · exact generatedTenth_root_two_certificates_packet_57_phase_checked
  · exact generatedTenth_root_two_certificates_packet_57_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_57_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
