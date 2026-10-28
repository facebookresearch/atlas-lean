/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket42SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket42TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket42VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket42PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket42CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket42KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 42: rows 2688 through 2751; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket42 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 42

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket42SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 42 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_42_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket42SourceMask := by
  exact generatedTenth_root_two_certificates_packet_42_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket42TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 42 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_42_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket42TargetMask := by
  exact generatedTenth_root_two_certificates_packet_42_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket42Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 42 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_42_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket42Vector := by
  exact generatedTenth_root_two_certificates_packet_42_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket42Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 42 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_42_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket42Phase := by
  exact generatedTenth_root_two_certificates_packet_42_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket42Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 42 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_42_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket42Coverage := by
  exact generatedTenth_root_two_certificates_packet_42_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket42Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 42 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_42_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket42Keys := by
  exact generatedTenth_root_two_certificates_packet_42_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_42
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket42SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket42TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket42Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket42Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket42Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket42Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket42 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_42_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket42 := by
  apply generatedTenth_root_two_certificates_packet_42
  · exact generatedTenth_root_two_certificates_packet_42_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_42_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_42_vector_checked
  · exact generatedTenth_root_two_certificates_packet_42_phase_checked
  · exact generatedTenth_root_two_certificates_packet_42_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_42_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
