/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket20SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket20TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket20VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket20PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket20CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket20KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 20: rows 1280 through 1343; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket20 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 20

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket20SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 20 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_20_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket20SourceMask := by
  exact generatedTenth_root_two_certificates_packet_20_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket20TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 20 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_20_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket20TargetMask := by
  exact generatedTenth_root_two_certificates_packet_20_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket20Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 20 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_20_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket20Vector := by
  exact generatedTenth_root_two_certificates_packet_20_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket20Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 20 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_20_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket20Phase := by
  exact generatedTenth_root_two_certificates_packet_20_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket20Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 20 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_20_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket20Coverage := by
  exact generatedTenth_root_two_certificates_packet_20_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket20Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 20 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_20_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket20Keys := by
  exact generatedTenth_root_two_certificates_packet_20_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_20
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket20SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket20TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket20Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket20Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket20Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket20Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket20 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_20_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket20 := by
  apply generatedTenth_root_two_certificates_packet_20
  · exact generatedTenth_root_two_certificates_packet_20_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_20_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_20_vector_checked
  · exact generatedTenth_root_two_certificates_packet_20_phase_checked
  · exact generatedTenth_root_two_certificates_packet_20_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_20_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
