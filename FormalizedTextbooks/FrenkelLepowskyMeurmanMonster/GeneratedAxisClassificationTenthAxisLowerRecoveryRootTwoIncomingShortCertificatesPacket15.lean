/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket15SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket15TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket15VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket15PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket15CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket15KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 15: rows 960 through 1023; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket15 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 15

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket15SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 15 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_15_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket15SourceMask := by
  exact generatedTenth_root_two_certificates_packet_15_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket15TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 15 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_15_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket15TargetMask := by
  exact generatedTenth_root_two_certificates_packet_15_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket15Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 15 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_15_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket15Vector := by
  exact generatedTenth_root_two_certificates_packet_15_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket15Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 15 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_15_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket15Phase := by
  exact generatedTenth_root_two_certificates_packet_15_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket15Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 15 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_15_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket15Coverage := by
  exact generatedTenth_root_two_certificates_packet_15_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket15Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 15 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_15_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket15Keys := by
  exact generatedTenth_root_two_certificates_packet_15_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_15
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket15SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket15TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket15Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket15Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket15Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket15Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket15 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_15_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket15 := by
  apply generatedTenth_root_two_certificates_packet_15
  · exact generatedTenth_root_two_certificates_packet_15_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_15_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_15_vector_checked
  · exact generatedTenth_root_two_certificates_packet_15_phase_checked
  · exact generatedTenth_root_two_certificates_packet_15_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_15_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
