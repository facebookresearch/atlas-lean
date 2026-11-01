/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket43SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket43TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket43VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket43PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket43CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket43KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 43: rows 2752 through 2815; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket43 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 43

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket43SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 43 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_43_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket43SourceMask := by
  exact generatedTenth_root_two_certificates_packet_43_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket43TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 43 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_43_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket43TargetMask := by
  exact generatedTenth_root_two_certificates_packet_43_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket43Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 43 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_43_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket43Vector := by
  exact generatedTenth_root_two_certificates_packet_43_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket43Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 43 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_43_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket43Phase := by
  exact generatedTenth_root_two_certificates_packet_43_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket43Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 43 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_43_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket43Coverage := by
  exact generatedTenth_root_two_certificates_packet_43_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket43Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 43 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_43_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket43Keys := by
  exact generatedTenth_root_two_certificates_packet_43_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_43
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket43SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket43TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket43Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket43Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket43Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket43Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket43 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_43_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket43 := by
  apply generatedTenth_root_two_certificates_packet_43
  · exact generatedTenth_root_two_certificates_packet_43_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_43_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_43_vector_checked
  · exact generatedTenth_root_two_certificates_packet_43_phase_checked
  · exact generatedTenth_root_two_certificates_packet_43_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_43_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
