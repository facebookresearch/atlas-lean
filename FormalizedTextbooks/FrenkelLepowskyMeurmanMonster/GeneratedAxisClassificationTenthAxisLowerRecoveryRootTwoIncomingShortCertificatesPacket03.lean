/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket03SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket03TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket03VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket03PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket03CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket03KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 03: rows 192 through 255; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket03 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 3

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket03SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 3 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_03_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket03SourceMask := by
  exact generatedTenth_root_two_certificates_packet_03_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket03TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 3 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_03_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket03TargetMask := by
  exact generatedTenth_root_two_certificates_packet_03_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket03Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 3 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_03_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket03Vector := by
  exact generatedTenth_root_two_certificates_packet_03_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket03Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 3 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_03_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket03Phase := by
  exact generatedTenth_root_two_certificates_packet_03_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket03Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 3 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_03_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket03Coverage := by
  exact generatedTenth_root_two_certificates_packet_03_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket03Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 3 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_03_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket03Keys := by
  exact generatedTenth_root_two_certificates_packet_03_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_03
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket03SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket03TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket03Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket03Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket03Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket03Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket03 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_03_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket03 := by
  apply generatedTenth_root_two_certificates_packet_03
  · exact generatedTenth_root_two_certificates_packet_03_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_03_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_03_vector_checked
  · exact generatedTenth_root_two_certificates_packet_03_phase_checked
  · exact generatedTenth_root_two_certificates_packet_03_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_03_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
