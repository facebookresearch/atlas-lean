/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket41SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket41TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket41VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket41PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket41CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket41KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 41: rows 2624 through 2687; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket41 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 41

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket41SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 41 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_41_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket41SourceMask := by
  exact generatedTenth_root_two_certificates_packet_41_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket41TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 41 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_41_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket41TargetMask := by
  exact generatedTenth_root_two_certificates_packet_41_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket41Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 41 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_41_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket41Vector := by
  exact generatedTenth_root_two_certificates_packet_41_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket41Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 41 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_41_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket41Phase := by
  exact generatedTenth_root_two_certificates_packet_41_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket41Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 41 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_41_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket41Coverage := by
  exact generatedTenth_root_two_certificates_packet_41_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket41Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 41 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_41_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket41Keys := by
  exact generatedTenth_root_two_certificates_packet_41_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_41
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket41SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket41TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket41Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket41Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket41Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket41Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket41 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_41_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket41 := by
  apply generatedTenth_root_two_certificates_packet_41
  · exact generatedTenth_root_two_certificates_packet_41_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_41_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_41_vector_checked
  · exact generatedTenth_root_two_certificates_packet_41_phase_checked
  · exact generatedTenth_root_two_certificates_packet_41_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_41_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
