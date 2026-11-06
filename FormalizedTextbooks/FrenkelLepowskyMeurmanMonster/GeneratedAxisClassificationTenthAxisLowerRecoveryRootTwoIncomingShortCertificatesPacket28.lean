/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket28SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket28TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket28VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket28PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket28CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket28KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 28: rows 1792 through 1855; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket28 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 28

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket28SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 28 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_28_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket28SourceMask := by
  exact generatedTenth_root_two_certificates_packet_28_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket28TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 28 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_28_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket28TargetMask := by
  exact generatedTenth_root_two_certificates_packet_28_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket28Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 28 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_28_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket28Vector := by
  exact generatedTenth_root_two_certificates_packet_28_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket28Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 28 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_28_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket28Phase := by
  exact generatedTenth_root_two_certificates_packet_28_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket28Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 28 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_28_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket28Coverage := by
  exact generatedTenth_root_two_certificates_packet_28_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket28Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 28 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_28_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket28Keys := by
  exact generatedTenth_root_two_certificates_packet_28_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_28
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket28SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket28TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket28Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket28Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket28Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket28Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket28 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_28_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket28 := by
  apply generatedTenth_root_two_certificates_packet_28
  · exact generatedTenth_root_two_certificates_packet_28_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_28_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_28_vector_checked
  · exact generatedTenth_root_two_certificates_packet_28_phase_checked
  · exact generatedTenth_root_two_certificates_packet_28_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_28_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
