/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket07SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket07TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket07VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket07PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket07CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket07KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 07: rows 448 through 511; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket07 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 7

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket07SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 7 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_07_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket07SourceMask := by
  exact generatedTenth_root_two_certificates_packet_07_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket07TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 7 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_07_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket07TargetMask := by
  exact generatedTenth_root_two_certificates_packet_07_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket07Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 7 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_07_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket07Vector := by
  exact generatedTenth_root_two_certificates_packet_07_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket07Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 7 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_07_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket07Phase := by
  exact generatedTenth_root_two_certificates_packet_07_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket07Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 7 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_07_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket07Coverage := by
  exact generatedTenth_root_two_certificates_packet_07_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket07Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 7 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_07_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket07Keys := by
  exact generatedTenth_root_two_certificates_packet_07_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_07
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket07SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket07TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket07Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket07Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket07Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket07Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket07 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_07_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket07 := by
  apply generatedTenth_root_two_certificates_packet_07
  · exact generatedTenth_root_two_certificates_packet_07_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_07_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_07_vector_checked
  · exact generatedTenth_root_two_certificates_packet_07_phase_checked
  · exact generatedTenth_root_two_certificates_packet_07_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_07_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
