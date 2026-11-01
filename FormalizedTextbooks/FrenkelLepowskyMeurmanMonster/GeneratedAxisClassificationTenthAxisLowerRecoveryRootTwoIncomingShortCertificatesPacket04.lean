/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket04SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket04TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket04VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket04PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket04CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket04KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 04: rows 256 through 319; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket04 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 4

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket04SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 4 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_04_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket04SourceMask := by
  exact generatedTenth_root_two_certificates_packet_04_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket04TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 4 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_04_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket04TargetMask := by
  exact generatedTenth_root_two_certificates_packet_04_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket04Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 4 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_04_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket04Vector := by
  exact generatedTenth_root_two_certificates_packet_04_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket04Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 4 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_04_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket04Phase := by
  exact generatedTenth_root_two_certificates_packet_04_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket04Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 4 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_04_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket04Coverage := by
  exact generatedTenth_root_two_certificates_packet_04_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket04Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 4 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_04_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket04Keys := by
  exact generatedTenth_root_two_certificates_packet_04_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_04
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket04SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket04TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket04Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket04Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket04Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket04Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket04 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_04_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket04 := by
  apply generatedTenth_root_two_certificates_packet_04
  · exact generatedTenth_root_two_certificates_packet_04_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_04_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_04_vector_checked
  · exact generatedTenth_root_two_certificates_packet_04_phase_checked
  · exact generatedTenth_root_two_certificates_packet_04_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_04_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
