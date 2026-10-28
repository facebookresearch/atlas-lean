/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket48SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket48TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket48VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket48PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket48CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket48KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 48: rows 3072 through 3135; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket48 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 48

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket48SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 48 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_48_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket48SourceMask := by
  exact generatedTenth_root_two_certificates_packet_48_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket48TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 48 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_48_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket48TargetMask := by
  exact generatedTenth_root_two_certificates_packet_48_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket48Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 48 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_48_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket48Vector := by
  exact generatedTenth_root_two_certificates_packet_48_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket48Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 48 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_48_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket48Phase := by
  exact generatedTenth_root_two_certificates_packet_48_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket48Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 48 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_48_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket48Coverage := by
  exact generatedTenth_root_two_certificates_packet_48_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket48Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 48 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_48_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket48Keys := by
  exact generatedTenth_root_two_certificates_packet_48_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_48
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket48SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket48TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket48Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket48Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket48Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket48Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket48 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_48_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket48 := by
  apply generatedTenth_root_two_certificates_packet_48
  · exact generatedTenth_root_two_certificates_packet_48_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_48_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_48_vector_checked
  · exact generatedTenth_root_two_certificates_packet_48_phase_checked
  · exact generatedTenth_root_two_certificates_packet_48_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_48_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
