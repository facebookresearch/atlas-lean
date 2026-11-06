/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket60SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket60TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket60VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket60PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket60CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket60KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 60: rows 3840 through 3903; dictionary count 16. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket60 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 60

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket60SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 60 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_60_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket60SourceMask := by
  exact generatedTenth_root_two_certificates_packet_60_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket60TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 60 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_60_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket60TargetMask := by
  exact generatedTenth_root_two_certificates_packet_60_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket60Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 60 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_60_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket60Vector := by
  exact generatedTenth_root_two_certificates_packet_60_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket60Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 60 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_60_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket60Phase := by
  exact generatedTenth_root_two_certificates_packet_60_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket60Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 60 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_60_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket60Coverage := by
  exact generatedTenth_root_two_certificates_packet_60_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket60Keys : Prop :=
  ∀ i : Fin 16, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 60 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_60_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket60Keys := by
  exact generatedTenth_root_two_certificates_packet_60_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_60
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket60SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket60TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket60Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket60Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket60Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket60Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket60 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_60_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket60 := by
  apply generatedTenth_root_two_certificates_packet_60
  · exact generatedTenth_root_two_certificates_packet_60_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_60_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_60_vector_checked
  · exact generatedTenth_root_two_certificates_packet_60_phase_checked
  · exact generatedTenth_root_two_certificates_packet_60_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_60_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
