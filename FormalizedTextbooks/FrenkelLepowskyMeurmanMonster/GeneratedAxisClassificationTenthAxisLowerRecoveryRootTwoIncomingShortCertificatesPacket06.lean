/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket06SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket06TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket06VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket06PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket06CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket06KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 06: rows 384 through 447; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket06 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 6

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket06SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 6 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_06_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket06SourceMask := by
  exact generatedTenth_root_two_certificates_packet_06_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket06TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 6 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_06_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket06TargetMask := by
  exact generatedTenth_root_two_certificates_packet_06_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket06Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 6 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_06_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket06Vector := by
  exact generatedTenth_root_two_certificates_packet_06_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket06Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 6 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_06_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket06Phase := by
  exact generatedTenth_root_two_certificates_packet_06_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket06Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 6 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_06_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket06Coverage := by
  exact generatedTenth_root_two_certificates_packet_06_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket06Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 6 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_06_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket06Keys := by
  exact generatedTenth_root_two_certificates_packet_06_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_06
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket06SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket06TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket06Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket06Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket06Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket06Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket06 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_06_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket06 := by
  apply generatedTenth_root_two_certificates_packet_06
  · exact generatedTenth_root_two_certificates_packet_06_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_06_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_06_vector_checked
  · exact generatedTenth_root_two_certificates_packet_06_phase_checked
  · exact generatedTenth_root_two_certificates_packet_06_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_06_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
