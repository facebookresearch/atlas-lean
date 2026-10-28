/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket11SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket11TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket11VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket11PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket11CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket11KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 11: rows 704 through 767; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket11 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 11

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket11SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 11 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_11_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket11SourceMask := by
  exact generatedTenth_root_two_certificates_packet_11_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket11TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 11 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_11_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket11TargetMask := by
  exact generatedTenth_root_two_certificates_packet_11_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket11Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 11 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_11_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket11Vector := by
  exact generatedTenth_root_two_certificates_packet_11_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket11Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 11 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_11_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket11Phase := by
  exact generatedTenth_root_two_certificates_packet_11_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket11Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 11 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_11_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket11Coverage := by
  exact generatedTenth_root_two_certificates_packet_11_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket11Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 11 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_11_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket11Keys := by
  exact generatedTenth_root_two_certificates_packet_11_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_11
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket11SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket11TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket11Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket11Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket11Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket11Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket11 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_11_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket11 := by
  apply generatedTenth_root_two_certificates_packet_11
  · exact generatedTenth_root_two_certificates_packet_11_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_11_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_11_vector_checked
  · exact generatedTenth_root_two_certificates_packet_11_phase_checked
  · exact generatedTenth_root_two_certificates_packet_11_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_11_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
