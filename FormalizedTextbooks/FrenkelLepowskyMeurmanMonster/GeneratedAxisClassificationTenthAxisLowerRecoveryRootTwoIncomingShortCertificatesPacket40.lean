/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket40SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket40TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket40VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket40PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket40CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket40KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 40: rows 2560 through 2623; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket40 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 40

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket40SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 40 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_40_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket40SourceMask := by
  exact generatedTenth_root_two_certificates_packet_40_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket40TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 40 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_40_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket40TargetMask := by
  exact generatedTenth_root_two_certificates_packet_40_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket40Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 40 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_40_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket40Vector := by
  exact generatedTenth_root_two_certificates_packet_40_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket40Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 40 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_40_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket40Phase := by
  exact generatedTenth_root_two_certificates_packet_40_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket40Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 40 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_40_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket40Coverage := by
  exact generatedTenth_root_two_certificates_packet_40_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket40Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 40 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_40_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket40Keys := by
  exact generatedTenth_root_two_certificates_packet_40_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_40
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket40SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket40TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket40Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket40Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket40Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket40Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket40 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_40_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket40 := by
  apply generatedTenth_root_two_certificates_packet_40
  · exact generatedTenth_root_two_certificates_packet_40_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_40_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_40_vector_checked
  · exact generatedTenth_root_two_certificates_packet_40_phase_checked
  · exact generatedTenth_root_two_certificates_packet_40_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_40_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
