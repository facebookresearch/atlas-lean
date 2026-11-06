/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket47SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket47TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket47VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket47PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket47CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket47KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 47: rows 3008 through 3071; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket47 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 47

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket47SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 47 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_47_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket47SourceMask := by
  exact generatedTenth_root_two_certificates_packet_47_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket47TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 47 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_47_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket47TargetMask := by
  exact generatedTenth_root_two_certificates_packet_47_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket47Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 47 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_47_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket47Vector := by
  exact generatedTenth_root_two_certificates_packet_47_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket47Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 47 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_47_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket47Phase := by
  exact generatedTenth_root_two_certificates_packet_47_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket47Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 47 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_47_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket47Coverage := by
  exact generatedTenth_root_two_certificates_packet_47_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket47Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 47 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_47_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket47Keys := by
  exact generatedTenth_root_two_certificates_packet_47_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_47
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket47SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket47TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket47Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket47Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket47Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket47Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket47 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_47_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket47 := by
  apply generatedTenth_root_two_certificates_packet_47
  · exact generatedTenth_root_two_certificates_packet_47_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_47_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_47_vector_checked
  · exact generatedTenth_root_two_certificates_packet_47_phase_checked
  · exact generatedTenth_root_two_certificates_packet_47_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_47_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
