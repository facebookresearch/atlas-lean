/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket39SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket39TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket39VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket39PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket39CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket39KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 39: rows 2496 through 2559; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket39 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 39

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket39SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 39 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_39_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket39SourceMask := by
  exact generatedTenth_root_two_certificates_packet_39_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket39TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 39 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_39_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket39TargetMask := by
  exact generatedTenth_root_two_certificates_packet_39_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket39Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 39 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_39_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket39Vector := by
  exact generatedTenth_root_two_certificates_packet_39_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket39Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 39 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_39_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket39Phase := by
  exact generatedTenth_root_two_certificates_packet_39_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket39Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 39 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_39_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket39Coverage := by
  exact generatedTenth_root_two_certificates_packet_39_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket39Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 39 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_39_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket39Keys := by
  exact generatedTenth_root_two_certificates_packet_39_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_39
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket39SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket39TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket39Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket39Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket39Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket39Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket39 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_39_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket39 := by
  apply generatedTenth_root_two_certificates_packet_39
  · exact generatedTenth_root_two_certificates_packet_39_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_39_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_39_vector_checked
  · exact generatedTenth_root_two_certificates_packet_39_phase_checked
  · exact generatedTenth_root_two_certificates_packet_39_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_39_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
