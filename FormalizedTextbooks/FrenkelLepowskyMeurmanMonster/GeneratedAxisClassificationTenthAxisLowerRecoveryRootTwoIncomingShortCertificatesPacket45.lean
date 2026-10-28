/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket45SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket45TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket45VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket45PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket45CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket45KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 45: rows 2880 through 2943; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket45 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 45

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket45SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 45 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_45_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket45SourceMask := by
  exact generatedTenth_root_two_certificates_packet_45_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket45TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 45 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_45_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket45TargetMask := by
  exact generatedTenth_root_two_certificates_packet_45_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket45Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 45 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_45_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket45Vector := by
  exact generatedTenth_root_two_certificates_packet_45_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket45Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 45 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_45_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket45Phase := by
  exact generatedTenth_root_two_certificates_packet_45_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket45Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 45 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_45_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket45Coverage := by
  exact generatedTenth_root_two_certificates_packet_45_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket45Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 45 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_45_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket45Keys := by
  exact generatedTenth_root_two_certificates_packet_45_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_45
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket45SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket45TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket45Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket45Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket45Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket45Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket45 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_45_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket45 := by
  apply generatedTenth_root_two_certificates_packet_45
  · exact generatedTenth_root_two_certificates_packet_45_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_45_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_45_vector_checked
  · exact generatedTenth_root_two_certificates_packet_45_phase_checked
  · exact generatedTenth_root_two_certificates_packet_45_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_45_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
