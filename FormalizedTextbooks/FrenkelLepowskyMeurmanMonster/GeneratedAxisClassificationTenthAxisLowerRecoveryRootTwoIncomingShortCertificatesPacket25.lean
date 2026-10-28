/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket25SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket25TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket25VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket25PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket25CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket25KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 25: rows 1600 through 1663; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket25 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 25

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket25SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 25 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_25_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket25SourceMask := by
  exact generatedTenth_root_two_certificates_packet_25_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket25TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 25 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_25_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket25TargetMask := by
  exact generatedTenth_root_two_certificates_packet_25_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket25Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 25 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_25_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket25Vector := by
  exact generatedTenth_root_two_certificates_packet_25_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket25Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 25 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_25_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket25Phase := by
  exact generatedTenth_root_two_certificates_packet_25_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket25Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 25 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_25_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket25Coverage := by
  exact generatedTenth_root_two_certificates_packet_25_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket25Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 25 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_25_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket25Keys := by
  exact generatedTenth_root_two_certificates_packet_25_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_25
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket25SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket25TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket25Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket25Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket25Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket25Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket25 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_25_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket25 := by
  apply generatedTenth_root_two_certificates_packet_25
  · exact generatedTenth_root_two_certificates_packet_25_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_25_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_25_vector_checked
  · exact generatedTenth_root_two_certificates_packet_25_phase_checked
  · exact generatedTenth_root_two_certificates_packet_25_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_25_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
