/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket56SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket56TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket56VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket56PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket56CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket56KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 56: rows 3584 through 3647; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket56 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 56

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket56SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 56 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_56_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket56SourceMask := by
  exact generatedTenth_root_two_certificates_packet_56_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket56TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 56 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_56_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket56TargetMask := by
  exact generatedTenth_root_two_certificates_packet_56_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket56Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 56 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_56_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket56Vector := by
  exact generatedTenth_root_two_certificates_packet_56_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket56Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 56 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_56_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket56Phase := by
  exact generatedTenth_root_two_certificates_packet_56_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket56Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 56 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_56_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket56Coverage := by
  exact generatedTenth_root_two_certificates_packet_56_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket56Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 56 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_56_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket56Keys := by
  exact generatedTenth_root_two_certificates_packet_56_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_56
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket56SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket56TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket56Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket56Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket56Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket56Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket56 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_56_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket56 := by
  apply generatedTenth_root_two_certificates_packet_56
  · exact generatedTenth_root_two_certificates_packet_56_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_56_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_56_vector_checked
  · exact generatedTenth_root_two_certificates_packet_56_phase_checked
  · exact generatedTenth_root_two_certificates_packet_56_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_56_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
