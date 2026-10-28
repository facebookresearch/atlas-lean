/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket51SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket51TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket51VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket51PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket51CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket51KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 51: rows 3264 through 3327; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket51 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 51

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket51SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 51 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_51_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket51SourceMask := by
  exact generatedTenth_root_two_certificates_packet_51_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket51TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 51 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_51_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket51TargetMask := by
  exact generatedTenth_root_two_certificates_packet_51_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket51Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 51 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_51_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket51Vector := by
  exact generatedTenth_root_two_certificates_packet_51_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket51Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 51 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_51_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket51Phase := by
  exact generatedTenth_root_two_certificates_packet_51_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket51Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 51 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_51_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket51Coverage := by
  exact generatedTenth_root_two_certificates_packet_51_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket51Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 51 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_51_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket51Keys := by
  exact generatedTenth_root_two_certificates_packet_51_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_51
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket51SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket51TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket51Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket51Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket51Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket51Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket51 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_51_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket51 := by
  apply generatedTenth_root_two_certificates_packet_51
  · exact generatedTenth_root_two_certificates_packet_51_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_51_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_51_vector_checked
  · exact generatedTenth_root_two_certificates_packet_51_phase_checked
  · exact generatedTenth_root_two_certificates_packet_51_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_51_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
