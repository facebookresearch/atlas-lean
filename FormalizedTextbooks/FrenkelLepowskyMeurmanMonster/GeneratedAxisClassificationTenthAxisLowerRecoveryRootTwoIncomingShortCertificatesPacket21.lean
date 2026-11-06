/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket21SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket21TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket21VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket21PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket21CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket21KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 21: rows 1344 through 1407; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket21 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 21

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket21SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 21 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_21_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket21SourceMask := by
  exact generatedTenth_root_two_certificates_packet_21_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket21TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 21 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_21_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket21TargetMask := by
  exact generatedTenth_root_two_certificates_packet_21_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket21Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 21 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_21_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket21Vector := by
  exact generatedTenth_root_two_certificates_packet_21_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket21Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 21 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_21_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket21Phase := by
  exact generatedTenth_root_two_certificates_packet_21_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket21Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 21 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_21_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket21Coverage := by
  exact generatedTenth_root_two_certificates_packet_21_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket21Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 21 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_21_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket21Keys := by
  exact generatedTenth_root_two_certificates_packet_21_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_21
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket21SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket21TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket21Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket21Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket21Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket21Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket21 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_21_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket21 := by
  apply generatedTenth_root_two_certificates_packet_21
  · exact generatedTenth_root_two_certificates_packet_21_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_21_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_21_vector_checked
  · exact generatedTenth_root_two_certificates_packet_21_phase_checked
  · exact generatedTenth_root_two_certificates_packet_21_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_21_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
