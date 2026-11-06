/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket50SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket50TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket50VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket50PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket50CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket50KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 50: rows 3200 through 3263; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket50 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 50

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket50SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 50 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_50_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket50SourceMask := by
  exact generatedTenth_root_two_certificates_packet_50_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket50TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 50 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_50_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket50TargetMask := by
  exact generatedTenth_root_two_certificates_packet_50_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket50Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 50 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_50_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket50Vector := by
  exact generatedTenth_root_two_certificates_packet_50_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket50Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 50 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_50_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket50Phase := by
  exact generatedTenth_root_two_certificates_packet_50_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket50Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 50 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_50_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket50Coverage := by
  exact generatedTenth_root_two_certificates_packet_50_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket50Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 50 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_50_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket50Keys := by
  exact generatedTenth_root_two_certificates_packet_50_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_50
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket50SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket50TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket50Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket50Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket50Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket50Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket50 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_50_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket50 := by
  apply generatedTenth_root_two_certificates_packet_50
  · exact generatedTenth_root_two_certificates_packet_50_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_50_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_50_vector_checked
  · exact generatedTenth_root_two_certificates_packet_50_phase_checked
  · exact generatedTenth_root_two_certificates_packet_50_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_50_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
