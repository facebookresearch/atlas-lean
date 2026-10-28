/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket19SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket19TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket19VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket19PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket19CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket19KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 19: rows 1216 through 1279; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket19 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 19

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket19SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 19 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_19_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket19SourceMask := by
  exact generatedTenth_root_two_certificates_packet_19_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket19TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 19 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_19_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket19TargetMask := by
  exact generatedTenth_root_two_certificates_packet_19_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket19Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 19 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_19_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket19Vector := by
  exact generatedTenth_root_two_certificates_packet_19_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket19Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 19 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_19_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket19Phase := by
  exact generatedTenth_root_two_certificates_packet_19_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket19Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 19 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_19_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket19Coverage := by
  exact generatedTenth_root_two_certificates_packet_19_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket19Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 19 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_19_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket19Keys := by
  exact generatedTenth_root_two_certificates_packet_19_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_19
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket19SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket19TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket19Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket19Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket19Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket19Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket19 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_19_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket19 := by
  apply generatedTenth_root_two_certificates_packet_19
  · exact generatedTenth_root_two_certificates_packet_19_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_19_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_19_vector_checked
  · exact generatedTenth_root_two_certificates_packet_19_phase_checked
  · exact generatedTenth_root_two_certificates_packet_19_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_19_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
