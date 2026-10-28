/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket27SourceMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket27TargetMaskLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket27VectorLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket27PhaseLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket27CoverageLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesPacket27KeysLeaf
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Packet 27: rows 1728 through 1791; dictionary count 64. -/
abbrev GeneratedTenthRootTwoIncomingShortCertificatesPacket27 :=
  GeneratedTenthRootTwoIncomingShortCertificatePacket 27

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket27SourceMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex 27 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_27_sourcemask_checked :
    GeneratedTenthRootTwoCertificatesPacket27SourceMask := by
  exact generatedTenth_root_two_certificates_packet_27_sourcemask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket27TargetMask : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex 27 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_27_targetmask_checked :
    GeneratedTenthRootTwoCertificatesPacket27TargetMask := by
  exact generatedTenth_root_two_certificates_packet_27_targetmask_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket27Vector : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex 27 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_27_vector_checked :
    GeneratedTenthRootTwoCertificatesPacket27Vector := by
  exact generatedTenth_root_two_certificates_packet_27_vector_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket27Phase : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex 27 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_27_phase_checked :
    GeneratedTenthRootTwoCertificatesPacket27Phase := by
  exact generatedTenth_root_two_certificates_packet_27_phase_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket27Coverage : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex 27 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_27_coverage_checked :
    GeneratedTenthRootTwoCertificatesPacket27Coverage := by
  exact generatedTenth_root_two_certificates_packet_27_coverage_leaf_checked

/-- Exact independent finite obligation, retaining its actual source bindings. -/
def GeneratedTenthRootTwoCertificatesPacket27Keys : Prop :=
  ∀ i : Fin 64, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex 27 i)

set_option maxRecDepth 100000 in
/-- Prospective closed kernel certificate; this draft has not been compiled. -/
theorem generatedTenth_root_two_certificates_packet_27_keys_checked :
    GeneratedTenthRootTwoCertificatesPacket27Keys := by
  exact generatedTenth_root_two_certificates_packet_27_keys_leaf_checked

/-- Separate proved obligations assemble this packet without dropping empty cases. -/
theorem generatedTenth_root_two_certificates_packet_27
    (hSourceMask : GeneratedTenthRootTwoCertificatesPacket27SourceMask)
    (hTargetMask : GeneratedTenthRootTwoCertificatesPacket27TargetMask)
    (hVector : GeneratedTenthRootTwoCertificatesPacket27Vector)
    (hPhase : GeneratedTenthRootTwoCertificatesPacket27Phase)
    (hCoverage : GeneratedTenthRootTwoCertificatesPacket27Coverage)
    (hKeys : GeneratedTenthRootTwoCertificatesPacket27Keys)
    : GeneratedTenthRootTwoIncomingShortCertificatesPacket27 := by
  exact ⟨hSourceMask, hTargetMask, hVector, hPhase, hCoverage, hKeys⟩

/-- Prospective complete packet, conditional on the six ungated proof drafts. -/
theorem generatedTenth_root_two_certificates_packet_27_checked :
    GeneratedTenthRootTwoIncomingShortCertificatesPacket27 := by
  apply generatedTenth_root_two_certificates_packet_27
  · exact generatedTenth_root_two_certificates_packet_27_sourcemask_checked
  · exact generatedTenth_root_two_certificates_packet_27_targetmask_checked
  · exact generatedTenth_root_two_certificates_packet_27_vector_checked
  · exact generatedTenth_root_two_certificates_packet_27_phase_checked
  · exact generatedTenth_root_two_certificates_packet_27_coverage_checked
  · exact generatedTenth_root_two_certificates_packet_27_keys_checked

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
