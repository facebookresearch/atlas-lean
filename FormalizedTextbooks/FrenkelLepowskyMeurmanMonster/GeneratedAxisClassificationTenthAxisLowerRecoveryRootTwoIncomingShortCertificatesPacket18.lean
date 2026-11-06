/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket18SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket18TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket18VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket18PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket18CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket18KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 18: rows 1152 through 1215; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket18 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 18

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket18SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 18 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_18_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket18SourceMask := by
  exact generatedTenth_root_two_certificates_packet_18_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket18TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 18 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_18_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket18TargetMask := by
  exact generatedTenth_root_two_certificates_packet_18_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket18Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 18 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_18_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket18Vector := by
  exact generatedTenth_root_two_certificates_packet_18_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket18Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 18 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_18_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket18Phase := by
  exact generatedTenth_root_two_certificates_packet_18_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket18Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 18 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_18_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket18Coverage := by
  exact generatedTenth_root_two_certificates_packet_18_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket18Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 18 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_18_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket18Keys := by
  exact generatedTenth_root_two_certificates_packet_18_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_18
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket18SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket18TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket18Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket18Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket18Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket18Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket18 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_18_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket18 := by
  apply generatedTenth_root_two_certificates_packet_18
  · exact generatedTenth_root_two_certificates_packet_18_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_18_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_18_vector_checked
  · exact generatedTenth_root_two_certificates_packet_18_phase_checked
  · exact generatedTenth_root_two_certificates_packet_18_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_18_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
