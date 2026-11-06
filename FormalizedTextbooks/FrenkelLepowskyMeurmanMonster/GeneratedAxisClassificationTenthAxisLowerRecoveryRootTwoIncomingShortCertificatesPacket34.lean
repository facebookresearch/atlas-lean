/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket34SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket34TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket34VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket34PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket34CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket34KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 34: rows 2176 through 2239; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket34 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 34

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket34SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 34 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_34_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket34SourceMask := by
  exact generatedTenth_root_two_certificates_packet_34_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket34TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 34 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_34_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket34TargetMask := by
  exact generatedTenth_root_two_certificates_packet_34_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket34Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 34 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_34_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket34Vector := by
  exact generatedTenth_root_two_certificates_packet_34_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket34Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 34 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_34_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket34Phase := by
  exact generatedTenth_root_two_certificates_packet_34_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket34Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 34 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_34_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket34Coverage := by
  exact generatedTenth_root_two_certificates_packet_34_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket34Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 34 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_34_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket34Keys := by
  exact generatedTenth_root_two_certificates_packet_34_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_34
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket34SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket34TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket34Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket34Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket34Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket34Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket34 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_34_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket34 := by
  apply generatedTenth_root_two_certificates_packet_34
  · exact generatedTenth_root_two_certificates_packet_34_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_34_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_34_vector_checked
  · exact generatedTenth_root_two_certificates_packet_34_phase_checked
  · exact generatedTenth_root_two_certificates_packet_34_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_34_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
