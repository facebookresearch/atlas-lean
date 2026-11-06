/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket52SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket52TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket52VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket52PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket52CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket52KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 52: rows 3328 through 3391; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket52 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 52

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket52SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 52 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_52_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket52SourceMask := by
  exact generatedTenth_root_two_certificates_packet_52_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket52TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 52 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_52_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket52TargetMask := by
  exact generatedTenth_root_two_certificates_packet_52_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket52Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 52 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_52_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket52Vector := by
  exact generatedTenth_root_two_certificates_packet_52_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket52Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 52 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_52_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket52Phase := by
  exact generatedTenth_root_two_certificates_packet_52_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket52Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 52 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_52_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket52Coverage := by
  exact generatedTenth_root_two_certificates_packet_52_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket52Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 52 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_52_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket52Keys := by
  exact generatedTenth_root_two_certificates_packet_52_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_52
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket52SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket52TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket52Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket52Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket52Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket52Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket52 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_52_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket52 := by
  apply generatedTenth_root_two_certificates_packet_52
  · exact generatedTenth_root_two_certificates_packet_52_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_52_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_52_vector_checked
  · exact generatedTenth_root_two_certificates_packet_52_phase_checked
  · exact generatedTenth_root_two_certificates_packet_52_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_52_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
