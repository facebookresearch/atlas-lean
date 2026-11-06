/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket44SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket44TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket44VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket44PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket44CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket44KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 44: rows 2816 through 2879; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket44 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 44

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket44SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 44 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_44_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket44SourceMask := by
  exact generatedTenth_root_two_certificates_packet_44_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket44TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 44 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_44_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket44TargetMask := by
  exact generatedTenth_root_two_certificates_packet_44_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket44Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 44 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_44_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket44Vector := by
  exact generatedTenth_root_two_certificates_packet_44_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket44Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 44 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_44_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket44Phase := by
  exact generatedTenth_root_two_certificates_packet_44_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket44Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 44 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_44_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket44Coverage := by
  exact generatedTenth_root_two_certificates_packet_44_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket44Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 44 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_44_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket44Keys := by
  exact generatedTenth_root_two_certificates_packet_44_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_44
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket44SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket44TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket44Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket44Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket44Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket44Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket44 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_44_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket44 := by
  apply generatedTenth_root_two_certificates_packet_44
  · exact generatedTenth_root_two_certificates_packet_44_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_44_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_44_vector_checked
  · exact generatedTenth_root_two_certificates_packet_44_phase_checked
  · exact generatedTenth_root_two_certificates_packet_44_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_44_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
