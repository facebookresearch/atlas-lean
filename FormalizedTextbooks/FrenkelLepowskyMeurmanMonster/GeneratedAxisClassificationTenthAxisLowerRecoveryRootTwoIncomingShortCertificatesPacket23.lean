/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket23SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket23TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket23VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket23PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket23CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket23KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 23: rows 1472 through 1535; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket23 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 23

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket23SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 23 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_23_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket23SourceMask := by
  exact generatedTenth_root_two_certificates_packet_23_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket23TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 23 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_23_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket23TargetMask := by
  exact generatedTenth_root_two_certificates_packet_23_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket23Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 23 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_23_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket23Vector := by
  exact generatedTenth_root_two_certificates_packet_23_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket23Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 23 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_23_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket23Phase := by
  exact generatedTenth_root_two_certificates_packet_23_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket23Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 23 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_23_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket23Coverage := by
  exact generatedTenth_root_two_certificates_packet_23_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket23Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 23 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_23_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket23Keys := by
  exact generatedTenth_root_two_certificates_packet_23_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_23
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket23SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket23TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket23Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket23Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket23Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket23Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket23 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_23_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket23 := by
  apply generatedTenth_root_two_certificates_packet_23
  · exact generatedTenth_root_two_certificates_packet_23_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_23_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_23_vector_checked
  · exact generatedTenth_root_two_certificates_packet_23_phase_checked
  · exact generatedTenth_root_two_certificates_packet_23_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_23_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
