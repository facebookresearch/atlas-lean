/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket26SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket26TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket26VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket26PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket26CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket26KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 26: rows 1664 through 1727; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket26 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 26

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket26SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 26 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_26_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket26SourceMask := by
  exact generatedTenth_root_two_certificates_packet_26_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket26TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 26 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_26_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket26TargetMask := by
  exact generatedTenth_root_two_certificates_packet_26_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket26Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 26 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_26_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket26Vector := by
  exact generatedTenth_root_two_certificates_packet_26_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket26Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 26 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_26_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket26Phase := by
  exact generatedTenth_root_two_certificates_packet_26_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket26Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 26 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_26_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket26Coverage := by
  exact generatedTenth_root_two_certificates_packet_26_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket26Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 26 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_26_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket26Keys := by
  exact generatedTenth_root_two_certificates_packet_26_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_26
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket26SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket26TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket26Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket26Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket26Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket26Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket26 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_26_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket26 := by
  apply generatedTenth_root_two_certificates_packet_26
  · exact generatedTenth_root_two_certificates_packet_26_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_26_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_26_vector_checked
  · exact generatedTenth_root_two_certificates_packet_26_phase_checked
  · exact generatedTenth_root_two_certificates_packet_26_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_26_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
