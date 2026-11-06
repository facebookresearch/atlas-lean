/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket46SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket46TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket46VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket46PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket46CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket46KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 46: rows 2944 through 3007; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket46 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 46

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket46SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 46 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_46_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket46SourceMask := by
  exact generatedTenth_root_two_certificates_packet_46_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket46TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 46 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_46_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket46TargetMask := by
  exact generatedTenth_root_two_certificates_packet_46_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket46Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 46 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_46_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket46Vector := by
  exact generatedTenth_root_two_certificates_packet_46_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket46Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 46 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_46_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket46Phase := by
  exact generatedTenth_root_two_certificates_packet_46_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket46Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 46 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_46_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket46Coverage := by
  exact generatedTenth_root_two_certificates_packet_46_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket46Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 46 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_46_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket46Keys := by
  exact generatedTenth_root_two_certificates_packet_46_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_46
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket46SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket46TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket46Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket46Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket46Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket46Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket46 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_46_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket46 := by
  apply generatedTenth_root_two_certificates_packet_46
  · exact generatedTenth_root_two_certificates_packet_46_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_46_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_46_vector_checked
  · exact generatedTenth_root_two_certificates_packet_46_phase_checked
  · exact generatedTenth_root_two_certificates_packet_46_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_46_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
