/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericMasks

/-! Ungated proof draft. No statement in this module has passed Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Absolute chronological index of a packet row; the last packet has forty rows. -/
def generatedTenthRootTwoCertificateRowIndex (p : Fin 65)
    (i : Fin (min 64 (4136 - p.val * 64))) : Fin 4136 :=
  ⟨p.val * 64 + i.val, by
    have hi := (lt_min_iff.mp i.isLt).2
    omega⟩

/-- Absolute dictionary index; packets after sixty contain no dictionary entries. -/
def generatedTenthRootTwoCertificateKeyIndex (p : Fin 65)
    (i : Fin (min 64 (3856 - p.val * 64))) : Fin 3856 :=
  ⟨p.val * 64 + i.val, by
    have hi := (lt_min_iff.mp i.isLt).2
    omega⟩

/-- Small independent packets retain all row, zero, and dictionary-default cases. -/
structure GeneratedTenthRootTwoIncomingShortCertificatePacket (p : Fin 65) : Prop where
  sourceMask : ∀ i, GeneratedTenthRootTwoCertificateSourceCheck
    (generatedTenthRootTwoCertificateRowIndex p i)
  targetMask : ∀ i, GeneratedTenthRootTwoCertificateTargetCheck
    (generatedTenthRootTwoCertificateRowIndex p i)
  vector : ∀ i, GeneratedTenthRootTwoCertificateVectorCheck
    (generatedTenthRootTwoCertificateRowIndex p i)
  phase : ∀ i, GeneratedTenthRootTwoCertificatePhaseCheck
    (generatedTenthRootTwoCertificateRowIndex p i)
  coverage : ∀ i, GeneratedTenthRootTwoCertificateCoverageCheck
    (generatedTenthRootTwoCertificateRowIndex p i)
  keys : ∀ i, GeneratedTenthRootTwoCertificateKeyCheck
    (generatedTenthRootTwoCertificateKeyIndex p i)

/-- No source row can be lost by partitioning its chronological address. -/
theorem generatedTenth_root_two_certificate_all_rows (P : Fin 4136 → Prop)
    (h : ∀ p : Fin 65, ∀ i, P (generatedTenthRootTwoCertificateRowIndex p i)) :
    ∀ k, P k := by
  intro k
  let p : Fin 65 := ⟨k.val / 64, by omega⟩
  let i : Fin (min 64 (4136 - p.val * 64)) := ⟨k.val % 64, by dsimp [p]; omega⟩
  have hk : generatedTenthRootTwoCertificateRowIndex p i = k := by
    apply Fin.ext
    dsimp [generatedTenthRootTwoCertificateRowIndex, p, i]
    omega
  exact hk ▸ h p i

/-- Every dictionary entry occurs once in its exact chronological packet. -/
theorem generatedTenth_root_two_certificate_all_keys (P : Fin 3856 → Prop)
    (h : ∀ p : Fin 65, ∀ i, P (generatedTenthRootTwoCertificateKeyIndex p i)) :
    ∀ a, P a := by
  intro a
  let p : Fin 65 := ⟨a.val / 64, by omega⟩
  let i : Fin (min 64 (3856 - p.val * 64)) := ⟨a.val % 64, by dsimp [p]; omega⟩
  have ha : generatedTenthRootTwoCertificateKeyIndex p i = a := by
    apply Fin.ext
    dsimp [generatedTenthRootTwoCertificateKeyIndex, p, i]
    omega
  exact ha ▸ h p i

/-- Explicit lengths and every small packet imply the original full incoming certificate. -/
theorem generatedTenth_root_two_certificate_of_packets
    (hd : generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowDescriptors.size = 4136)
    (hw : generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryWords.size = 3856)
    (hp : ∀ p : Fin 65, GeneratedTenthRootTwoIncomingShortCertificatePacket p) :
    GeneratedTenthRootTwoIncomingShortCertificate := by
  refine ⟨hd, hw, ?_, ?_, ?_⟩
  · exact generatedTenth_root_two_certificate_all_keys _ (fun p => (hp p).keys)
  · intro k
    exact (generatedTenth_root_two_certificate_all_rows _ (fun p => (hp p).coverage) k).trans
      (generatedTenth_root_two_certificate_signed_numerator k)
  · intro k
    apply generatedTenth_root_two_certificate_row_of_checks k
    · exact generatedTenth_root_two_certificate_all_rows _ (fun p => (hp p).sourceMask) k
    · exact generatedTenth_root_two_certificate_all_rows _ (fun p => (hp p).targetMask) k
    · exact generatedTenth_root_two_certificate_all_rows _ (fun p => (hp p).vector) k
    · exact generatedTenth_root_two_certificate_all_rows _ (fun p => (hp p).phase) k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
