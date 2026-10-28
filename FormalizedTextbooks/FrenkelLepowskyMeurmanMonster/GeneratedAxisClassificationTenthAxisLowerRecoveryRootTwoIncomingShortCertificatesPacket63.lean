/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket63SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket63TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket63VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket63PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket63CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket63KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 63: rows 4032 through 4095; dictionary count 0. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket63 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 63

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket63SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 63 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_63_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket63SourceMask := by
  exact generatedTenth_root_two_certificates_packet_63_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket63TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 63 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_63_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket63TargetMask := by
  exact generatedTenth_root_two_certificates_packet_63_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket63Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 63 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_63_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket63Vector := by
  exact generatedTenth_root_two_certificates_packet_63_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket63Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 63 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_63_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket63Phase := by
  exact generatedTenth_root_two_certificates_packet_63_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket63Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 63 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_63_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket63Coverage := by
  exact generatedTenth_root_two_certificates_packet_63_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket63Keys : Prop :=
  ∀ i : Fin 0, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 63 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_63_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket63Keys := by
  exact generatedTenth_root_two_certificates_packet_63_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_63
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket63SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket63TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket63Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket63Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket63Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket63Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket63 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_63_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket63 := by
  apply generatedTenth_root_two_certificates_packet_63
  · exact generatedTenth_root_two_certificates_packet_63_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_63_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_63_vector_checked
  · exact generatedTenth_root_two_certificates_packet_63_phase_checked
  · exact generatedTenth_root_two_certificates_packet_63_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_63_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
