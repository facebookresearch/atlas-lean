/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket59SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket59TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket59VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket59PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket59CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket59KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 59: rows 3776 through 3839; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket59 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 59

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket59SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 59 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_59_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket59SourceMask := by
  exact generatedTenth_root_two_certificates_packet_59_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket59TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 59 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_59_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket59TargetMask := by
  exact generatedTenth_root_two_certificates_packet_59_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket59Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 59 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_59_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket59Vector := by
  exact generatedTenth_root_two_certificates_packet_59_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket59Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 59 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_59_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket59Phase := by
  exact generatedTenth_root_two_certificates_packet_59_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket59Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 59 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_59_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket59Coverage := by
  exact generatedTenth_root_two_certificates_packet_59_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket59Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 59 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_59_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket59Keys := by
  exact generatedTenth_root_two_certificates_packet_59_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_59
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket59SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket59TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket59Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket59Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket59Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket59Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket59 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_59_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket59 := by
  apply generatedTenth_root_two_certificates_packet_59
  · exact generatedTenth_root_two_certificates_packet_59_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_59_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_59_vector_checked
  · exact generatedTenth_root_two_certificates_packet_59_phase_checked
  · exact generatedTenth_root_two_certificates_packet_59_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_59_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
