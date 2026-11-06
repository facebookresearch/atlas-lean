/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket36SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket36TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket36VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket36PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket36CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket36KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 36: rows 2304 through 2367; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket36 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 36

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket36SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 36 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_36_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket36SourceMask := by
  exact generatedTenth_root_two_certificates_packet_36_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket36TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 36 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_36_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket36TargetMask := by
  exact generatedTenth_root_two_certificates_packet_36_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket36Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 36 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_36_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket36Vector := by
  exact generatedTenth_root_two_certificates_packet_36_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket36Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 36 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_36_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket36Phase := by
  exact generatedTenth_root_two_certificates_packet_36_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket36Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 36 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_36_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket36Coverage := by
  exact generatedTenth_root_two_certificates_packet_36_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket36Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 36 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_36_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket36Keys := by
  exact generatedTenth_root_two_certificates_packet_36_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_36
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket36SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket36TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket36Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket36Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket36Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket36Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket36 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_36_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket36 := by
  apply generatedTenth_root_two_certificates_packet_36
  · exact generatedTenth_root_two_certificates_packet_36_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_36_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_36_vector_checked
  · exact generatedTenth_root_two_certificates_packet_36_phase_checked
  · exact generatedTenth_root_two_certificates_packet_36_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_36_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
