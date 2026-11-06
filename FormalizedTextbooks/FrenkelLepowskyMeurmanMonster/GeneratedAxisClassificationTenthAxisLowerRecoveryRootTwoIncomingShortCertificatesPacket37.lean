/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket37SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket37TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket37VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket37PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket37CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket37KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 37: rows 2368 through 2431; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket37 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 37

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket37SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 37 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_37_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket37SourceMask := by
  exact generatedTenth_root_two_certificates_packet_37_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket37TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 37 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_37_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket37TargetMask := by
  exact generatedTenth_root_two_certificates_packet_37_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket37Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 37 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_37_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket37Vector := by
  exact generatedTenth_root_two_certificates_packet_37_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket37Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 37 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_37_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket37Phase := by
  exact generatedTenth_root_two_certificates_packet_37_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket37Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 37 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_37_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket37Coverage := by
  exact generatedTenth_root_two_certificates_packet_37_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket37Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 37 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_37_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket37Keys := by
  exact generatedTenth_root_two_certificates_packet_37_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_37
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket37SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket37TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket37Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket37Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket37Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket37Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket37 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_37_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket37 := by
  apply generatedTenth_root_two_certificates_packet_37
  · exact generatedTenth_root_two_certificates_packet_37_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_37_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_37_vector_checked
  · exact generatedTenth_root_two_certificates_packet_37_phase_checked
  · exact generatedTenth_root_two_certificates_packet_37_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_37_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
