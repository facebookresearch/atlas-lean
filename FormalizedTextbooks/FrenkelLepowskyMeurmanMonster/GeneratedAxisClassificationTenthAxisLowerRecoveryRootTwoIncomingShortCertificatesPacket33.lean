/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket33SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket33TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket33VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket33PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket33CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket33KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 33: rows 2112 through 2175; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket33 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 33

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket33SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 33 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_33_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket33SourceMask := by
  exact generatedTenth_root_two_certificates_packet_33_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket33TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 33 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_33_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket33TargetMask := by
  exact generatedTenth_root_two_certificates_packet_33_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket33Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 33 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_33_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket33Vector := by
  exact generatedTenth_root_two_certificates_packet_33_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket33Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 33 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_33_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket33Phase := by
  exact generatedTenth_root_two_certificates_packet_33_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket33Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 33 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_33_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket33Coverage := by
  exact generatedTenth_root_two_certificates_packet_33_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket33Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 33 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_33_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket33Keys := by
  exact generatedTenth_root_two_certificates_packet_33_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_33
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket33SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket33TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket33Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket33Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket33Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket33Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket33 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_33_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket33 := by
  apply generatedTenth_root_two_certificates_packet_33
  · exact generatedTenth_root_two_certificates_packet_33_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_33_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_33_vector_checked
  · exact generatedTenth_root_two_certificates_packet_33_phase_checked
  · exact generatedTenth_root_two_certificates_packet_33_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_33_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
