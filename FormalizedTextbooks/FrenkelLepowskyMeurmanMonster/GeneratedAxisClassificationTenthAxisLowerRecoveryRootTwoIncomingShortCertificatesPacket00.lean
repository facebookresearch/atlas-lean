/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket00SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket00TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket00VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket00PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket00CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket00KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortPacketRewriteGeneric

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 00: rows 0 through 63; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket00 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 0

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket00SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 0 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_00_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket00SourceMask := by
  exact generatedTenth_root_two_certificates_packet_00_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket00TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 0 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_00_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket00TargetMask := by
  exact generatedTenth_root_two_certificates_packet_00_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket00Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 0 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_00_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket00Vector := by
  exact generatedTenth_root_two_certificates_packet_00_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket00Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 0 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_00_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket00Phase := by
  exact generatedTenth_root_two_certificates_packet_00_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket00Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 0 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_00_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket00Coverage := by
  exact generatedTenth_root_two_certificates_packet_00_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket00Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 0 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_00_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket00Keys := by
  exact generatedTenth_root_two_certificates_packet_00_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_00
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket00SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket00TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket00Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket00Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket00Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket00Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket00 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_00_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket00 := by
  apply generatedTenth_root_two_certificates_packet_00
  · exact generatedTenth_root_two_certificates_packet_00_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_00_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_00_vector_checked
  · exact generatedTenth_root_two_certificates_packet_00_phase_checked
  · exact generatedTenth_root_two_certificates_packet_00_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_00_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
