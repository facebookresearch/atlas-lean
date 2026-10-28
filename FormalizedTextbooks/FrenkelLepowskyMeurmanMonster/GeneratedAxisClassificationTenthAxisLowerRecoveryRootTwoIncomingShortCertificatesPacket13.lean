/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket13SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket13TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket13VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket13PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket13CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket13KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 13: rows 832 through 895; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket13 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 13

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket13SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 13 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_13_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket13SourceMask := by
  exact generatedTenth_root_two_certificates_packet_13_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket13TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 13 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_13_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket13TargetMask := by
  exact generatedTenth_root_two_certificates_packet_13_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket13Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 13 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_13_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket13Vector := by
  exact generatedTenth_root_two_certificates_packet_13_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket13Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 13 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_13_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket13Phase := by
  exact generatedTenth_root_two_certificates_packet_13_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket13Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 13 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_13_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket13Coverage := by
  exact generatedTenth_root_two_certificates_packet_13_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket13Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 13 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_13_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket13Keys := by
  exact generatedTenth_root_two_certificates_packet_13_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_13
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket13SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket13TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket13Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket13Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket13Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket13Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket13 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_13_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket13 := by
  apply generatedTenth_root_two_certificates_packet_13
  · exact generatedTenth_root_two_certificates_packet_13_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_13_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_13_vector_checked
  · exact generatedTenth_root_two_certificates_packet_13_phase_checked
  · exact generatedTenth_root_two_certificates_packet_13_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_13_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
