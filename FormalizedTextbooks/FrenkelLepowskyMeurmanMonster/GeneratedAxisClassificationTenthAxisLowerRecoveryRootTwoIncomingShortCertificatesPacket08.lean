/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket08SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket08TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket08VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket08PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket08CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket08KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 08: rows 512 through 575; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket08 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 8

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket08SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 8 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_08_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket08SourceMask := by
  exact generatedTenth_root_two_certificates_packet_08_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket08TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 8 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_08_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket08TargetMask := by
  exact generatedTenth_root_two_certificates_packet_08_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket08Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 8 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_08_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket08Vector := by
  exact generatedTenth_root_two_certificates_packet_08_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket08Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 8 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_08_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket08Phase := by
  exact generatedTenth_root_two_certificates_packet_08_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket08Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 8 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_08_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket08Coverage := by
  exact generatedTenth_root_two_certificates_packet_08_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket08Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 8 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_08_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket08Keys := by
  exact generatedTenth_root_two_certificates_packet_08_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_08
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket08SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket08TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket08Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket08Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket08Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket08Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket08 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_08_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket08 := by
  apply generatedTenth_root_two_certificates_packet_08
  · exact generatedTenth_root_two_certificates_packet_08_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_08_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_08_vector_checked
  · exact generatedTenth_root_two_certificates_packet_08_phase_checked
  · exact generatedTenth_root_two_certificates_packet_08_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_08_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
