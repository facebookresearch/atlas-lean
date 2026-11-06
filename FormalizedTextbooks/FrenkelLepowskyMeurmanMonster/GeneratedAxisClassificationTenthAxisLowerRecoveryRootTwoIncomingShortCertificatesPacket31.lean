/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket31SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket31TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket31VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket31PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket31CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket31KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 31: rows 1984 through 2047; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket31 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 31

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket31SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 31 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_31_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket31SourceMask := by
  exact generatedTenth_root_two_certificates_packet_31_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket31TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 31 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_31_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket31TargetMask := by
  exact generatedTenth_root_two_certificates_packet_31_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket31Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 31 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_31_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket31Vector := by
  exact generatedTenth_root_two_certificates_packet_31_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket31Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 31 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_31_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket31Phase := by
  exact generatedTenth_root_two_certificates_packet_31_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket31Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 31 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_31_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket31Coverage := by
  exact generatedTenth_root_two_certificates_packet_31_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket31Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 31 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_31_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket31Keys := by
  exact generatedTenth_root_two_certificates_packet_31_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_31
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket31SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket31TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket31Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket31Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket31Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket31Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket31 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_31_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket31 := by
  apply generatedTenth_root_two_certificates_packet_31
  · exact generatedTenth_root_two_certificates_packet_31_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_31_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_31_vector_checked
  · exact generatedTenth_root_two_certificates_packet_31_phase_checked
  · exact generatedTenth_root_two_certificates_packet_31_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_31_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
