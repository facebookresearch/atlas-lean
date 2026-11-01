/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket62SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket62TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket62VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket62PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket62CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket62KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 62: rows 3968 through 4031; dictionary count 0. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket62 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 62

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket62SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 62 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_62_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket62SourceMask := by
  exact generatedTenth_root_two_certificates_packet_62_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket62TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 62 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_62_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket62TargetMask := by
  exact generatedTenth_root_two_certificates_packet_62_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket62Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 62 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_62_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket62Vector := by
  exact generatedTenth_root_two_certificates_packet_62_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket62Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 62 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_62_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket62Phase := by
  exact generatedTenth_root_two_certificates_packet_62_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket62Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 62 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_62_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket62Coverage := by
  exact generatedTenth_root_two_certificates_packet_62_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket62Keys : Prop :=
  ∀ i : Fin 0, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 62 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_62_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket62Keys := by
  exact generatedTenth_root_two_certificates_packet_62_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_62
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket62SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket62TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket62Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket62Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket62Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket62Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket62 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_62_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket62 := by
  apply generatedTenth_root_two_certificates_packet_62
  · exact generatedTenth_root_two_certificates_packet_62_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_62_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_62_vector_checked
  · exact generatedTenth_root_two_certificates_packet_62_phase_checked
  · exact generatedTenth_root_two_certificates_packet_62_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_62_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
