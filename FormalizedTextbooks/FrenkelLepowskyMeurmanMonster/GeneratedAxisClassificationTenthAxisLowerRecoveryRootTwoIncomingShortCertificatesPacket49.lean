/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket49SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket49TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket49VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket49PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket49CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket49KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 49: rows 3136 through 3199; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket49 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 49

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket49SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 49 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_49_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket49SourceMask := by
  exact generatedTenth_root_two_certificates_packet_49_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket49TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 49 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_49_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket49TargetMask := by
  exact generatedTenth_root_two_certificates_packet_49_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket49Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 49 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_49_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket49Vector := by
  exact generatedTenth_root_two_certificates_packet_49_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket49Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 49 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_49_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket49Phase := by
  exact generatedTenth_root_two_certificates_packet_49_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket49Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 49 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_49_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket49Coverage := by
  exact generatedTenth_root_two_certificates_packet_49_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket49Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 49 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_49_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket49Keys := by
  exact generatedTenth_root_two_certificates_packet_49_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_49
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket49SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket49TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket49Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket49Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket49Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket49Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket49 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_49_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket49 := by
  apply generatedTenth_root_two_certificates_packet_49
  · exact generatedTenth_root_two_certificates_packet_49_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_49_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_49_vector_checked
  · exact generatedTenth_root_two_certificates_packet_49_phase_checked
  · exact generatedTenth_root_two_certificates_packet_49_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_49_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
