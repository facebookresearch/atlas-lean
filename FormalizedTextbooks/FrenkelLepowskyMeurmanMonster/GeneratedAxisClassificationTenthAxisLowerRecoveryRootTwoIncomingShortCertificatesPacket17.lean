/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket17SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket17TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket17VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket17PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket17CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket17KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 17: rows 1088 through 1151; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket17 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 17

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket17SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 17 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_17_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket17SourceMask := by
  exact generatedTenth_root_two_certificates_packet_17_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket17TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 17 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_17_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket17TargetMask := by
  exact generatedTenth_root_two_certificates_packet_17_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket17Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 17 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_17_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket17Vector := by
  exact generatedTenth_root_two_certificates_packet_17_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket17Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 17 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_17_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket17Phase := by
  exact generatedTenth_root_two_certificates_packet_17_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket17Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 17 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_17_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket17Coverage := by
  exact generatedTenth_root_two_certificates_packet_17_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket17Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 17 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_17_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket17Keys := by
  exact generatedTenth_root_two_certificates_packet_17_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_17
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket17SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket17TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket17Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket17Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket17Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket17Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket17 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_17_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket17 := by
  apply generatedTenth_root_two_certificates_packet_17
  · exact generatedTenth_root_two_certificates_packet_17_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_17_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_17_vector_checked
  · exact generatedTenth_root_two_certificates_packet_17_phase_checked
  · exact generatedTenth_root_two_certificates_packet_17_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_17_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
