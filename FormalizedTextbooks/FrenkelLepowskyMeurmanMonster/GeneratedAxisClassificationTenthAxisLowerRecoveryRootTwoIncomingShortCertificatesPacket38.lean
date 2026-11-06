/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket38SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket38TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket38VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket38PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket38CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket38KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 38: rows 2432 through 2495; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket38 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 38

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket38SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 38 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_38_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket38SourceMask := by
  exact generatedTenth_root_two_certificates_packet_38_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket38TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 38 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_38_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket38TargetMask := by
  exact generatedTenth_root_two_certificates_packet_38_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket38Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 38 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_38_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket38Vector := by
  exact generatedTenth_root_two_certificates_packet_38_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket38Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 38 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_38_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket38Phase := by
  exact generatedTenth_root_two_certificates_packet_38_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket38Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 38 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_38_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket38Coverage := by
  exact generatedTenth_root_two_certificates_packet_38_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket38Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 38 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_38_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket38Keys := by
  exact generatedTenth_root_two_certificates_packet_38_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_38
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket38SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket38TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket38Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket38Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket38Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket38Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket38 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_38_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket38 := by
  apply generatedTenth_root_two_certificates_packet_38
  · exact generatedTenth_root_two_certificates_packet_38_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_38_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_38_vector_checked
  · exact generatedTenth_root_two_certificates_packet_38_phase_checked
  · exact generatedTenth_root_two_certificates_packet_38_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_38_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
