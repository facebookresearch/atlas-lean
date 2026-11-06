/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket09SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket09TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket09VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket09PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket09CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket09KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 09: rows 576 through 639; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket09 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 9

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket09SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 9 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_09_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket09SourceMask := by
  exact generatedTenth_root_two_certificates_packet_09_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket09TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 9 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_09_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket09TargetMask := by
  exact generatedTenth_root_two_certificates_packet_09_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket09Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 9 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_09_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket09Vector := by
  exact generatedTenth_root_two_certificates_packet_09_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket09Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 9 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_09_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket09Phase := by
  exact generatedTenth_root_two_certificates_packet_09_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket09Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 9 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_09_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket09Coverage := by
  exact generatedTenth_root_two_certificates_packet_09_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket09Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 9 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_09_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket09Keys := by
  exact generatedTenth_root_two_certificates_packet_09_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_09
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket09SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket09TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket09Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket09Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket09Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket09Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket09 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_09_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket09 := by
  apply generatedTenth_root_two_certificates_packet_09
  · exact generatedTenth_root_two_certificates_packet_09_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_09_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_09_vector_checked
  · exact generatedTenth_root_two_certificates_packet_09_phase_checked
  · exact generatedTenth_root_two_certificates_packet_09_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_09_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
