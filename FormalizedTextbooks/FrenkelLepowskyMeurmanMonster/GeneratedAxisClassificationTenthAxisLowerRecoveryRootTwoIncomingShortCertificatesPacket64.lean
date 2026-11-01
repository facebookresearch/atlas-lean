/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket64SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket64TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket64VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket64PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket64CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket64KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 64: rows 4096 through 4135; dictionary count 0. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket64 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 64

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket64SourceMask : Prop :=
  ∀ i : Fin 40, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 64 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_64_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket64SourceMask := by
  exact generatedTenth_root_two_certificates_packet_64_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket64TargetMask : Prop :=
  ∀ i : Fin 40, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 64 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_64_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket64TargetMask := by
  exact generatedTenth_root_two_certificates_packet_64_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket64Vector : Prop :=
  ∀ i : Fin 40, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 64 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_64_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket64Vector := by
  exact generatedTenth_root_two_certificates_packet_64_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket64Phase : Prop :=
  ∀ i : Fin 40, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 64 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_64_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket64Phase := by
  exact generatedTenth_root_two_certificates_packet_64_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket64Coverage : Prop :=
  ∀ i : Fin 40, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 64 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_64_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket64Coverage := by
  exact generatedTenth_root_two_certificates_packet_64_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket64Keys : Prop :=
  ∀ i : Fin 0, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 64 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_64_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket64Keys := by
  exact generatedTenth_root_two_certificates_packet_64_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_64
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket64SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket64TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket64Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket64Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket64Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket64Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket64 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_64_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket64 := by
  apply generatedTenth_root_two_certificates_packet_64
  · exact generatedTenth_root_two_certificates_packet_64_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_64_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_64_vector_checked
  · exact generatedTenth_root_two_certificates_packet_64_phase_checked
  · exact generatedTenth_root_two_certificates_packet_64_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_64_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
