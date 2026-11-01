/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket61SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket61TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket61VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket61PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket61CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket61KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 61: rows 3904 through 3967; dictionary count 0. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket61 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 61

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket61SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 61 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_61_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket61SourceMask := by
  exact generatedTenth_root_two_certificates_packet_61_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket61TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 61 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_61_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket61TargetMask := by
  exact generatedTenth_root_two_certificates_packet_61_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket61Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 61 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_61_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket61Vector := by
  exact generatedTenth_root_two_certificates_packet_61_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket61Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 61 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_61_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket61Phase := by
  exact generatedTenth_root_two_certificates_packet_61_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket61Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 61 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_61_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket61Coverage := by
  exact generatedTenth_root_two_certificates_packet_61_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket61Keys : Prop :=
  ∀ i : Fin 0, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 61 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_61_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket61Keys := by
  exact generatedTenth_root_two_certificates_packet_61_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_61
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket61SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket61TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket61Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket61Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket61Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket61Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket61 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_61_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket61 := by
  apply generatedTenth_root_two_certificates_packet_61
  · exact generatedTenth_root_two_certificates_packet_61_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_61_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_61_vector_checked
  · exact generatedTenth_root_two_certificates_packet_61_phase_checked
  · exact generatedTenth_root_two_certificates_packet_61_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_61_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
