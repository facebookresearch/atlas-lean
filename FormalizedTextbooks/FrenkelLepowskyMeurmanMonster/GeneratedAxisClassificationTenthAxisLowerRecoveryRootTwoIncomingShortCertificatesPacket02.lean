/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket02SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket02TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket02VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket02PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket02CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket02KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 02: rows 128 through 191; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket02 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 2

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket02SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 2 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_02_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket02SourceMask := by
  exact generatedTenth_root_two_certificates_packet_02_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket02TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 2 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_02_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket02TargetMask := by
  exact generatedTenth_root_two_certificates_packet_02_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket02Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 2 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_02_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket02Vector := by
  exact generatedTenth_root_two_certificates_packet_02_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket02Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 2 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_02_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket02Phase := by
  exact generatedTenth_root_two_certificates_packet_02_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket02Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 2 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_02_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket02Coverage := by
  exact generatedTenth_root_two_certificates_packet_02_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket02Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 2 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_02_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket02Keys := by
  exact generatedTenth_root_two_certificates_packet_02_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_02
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket02SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket02TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket02Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket02Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket02Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket02Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket02 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_02_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket02 := by
  apply generatedTenth_root_two_certificates_packet_02
  · exact generatedTenth_root_two_certificates_packet_02_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_02_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_02_vector_checked
  · exact generatedTenth_root_two_certificates_packet_02_phase_checked
  · exact generatedTenth_root_two_certificates_packet_02_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_02_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
