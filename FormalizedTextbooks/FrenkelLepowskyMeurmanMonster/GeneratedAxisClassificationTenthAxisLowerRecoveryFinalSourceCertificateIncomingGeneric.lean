/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceCertificateIncomingData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortData

/-! Ungated packed access to original dictionary fields; the original balanced tree is reused. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original dictionary fields use balanced 16 by 16 word lookup, with sixteen fields per word. -/
def generatedTenthFinalSourceCertificateIncomingField
    (words : Fin 16 → Fin 16 → ℕ) (bits : ℕ) (a : Fin 3856) : ℕ :=
  (words ⟨a.val / 256, by omega⟩ ⟨a.val / 16 % 16, Nat.mod_lt _ (by decide)⟩ >>>
    (bits * (a.val % 16))) % 2 ^ bits

/-- Exact packed original dictionary address field. -/
def generatedTenthFinalSourceCertificateIncomingKey (a : Fin 3856) : ℕ :=
  generatedTenthFinalSourceCertificateIncomingField
    generatedTenthFinalSourceCertificateIncomingKeyWords 17 a

/-- Exact signed original dictionary numerator field. -/
def generatedTenthFinalSourceCertificateIncomingNumerator (a : Fin 3856) : ℤ :=
  (generatedTenthFinalSourceCertificateIncomingField
    generatedTenthFinalSourceCertificateIncomingNumeratorWords 8 a : ℤ) - 128

/-- Both original fields are certified before the shared balanced dictionary is used. -/
def GeneratedTenthFinalSourceCertificateIncomingEntry (a : Fin 3856) : Prop :=
  generatedTenthFinalSourceCertificateIncomingKey a =
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryKey a ∧
  generatedTenthFinalSourceCertificateIncomingNumerator a =
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryNumerator a

/-- The shared original tree keeps all outside-support zero defaults exactly. -/
def generatedTenthFinalSourceCertificateIncomingC (r : GriessShortIndex) : ℤ :=
  match generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryTree.lookup
      generatedTenthFinalSourceCertificateIncomingKey
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortAddress r) with
  | none => 0
  | some a => generatedTenthFinalSourceCertificateIncomingNumerator a

/-- Exact field equality gives whole incoming C equality, including every zero coordinate. -/
theorem generatedTenth_final_source_certificate_incoming_eq
    (h : ∀ a, GeneratedTenthFinalSourceCertificateIncomingEntry a) (r : GriessShortIndex) :
    generatedTenthFinalSourceCertificateIncomingC r =
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient r := by
  have hk : generatedTenthFinalSourceCertificateIncomingKey =
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryKey := funext (fun a => (h a).1)
  have hn : generatedTenthFinalSourceCertificateIncomingNumerator =
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryNumerator :=
    funext (fun a => (h a).2)
  simp only [generatedTenthFinalSourceCertificateIncomingC,
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient, hk, hn]
  rfl

/-- Original full sixty-four entry packet address. -/
def generatedTenthFinalSourceCertificateIncomingLabel (b : Fin 60) (u : Fin 64) : Fin 3856 :=
  ⟨64 * b.val + u.val, by omega⟩

/-- Original final sixteen dictionary addresses. -/
def generatedTenthFinalSourceCertificateIncomingTail (u : Fin 16) : Fin 3856 :=
  ⟨3840 + u.val, by omega⟩

/-- Sixty full packets and the exact sixteen-entry tail cover the original dictionary. -/
theorem generatedTenth_final_source_certificate_incoming_of_blocks
    (h : ∀ b u, GeneratedTenthFinalSourceCertificateIncomingEntry
      (generatedTenthFinalSourceCertificateIncomingLabel b u))
    (ht : ∀ u, GeneratedTenthFinalSourceCertificateIncomingEntry
      (generatedTenthFinalSourceCertificateIncomingTail u)) :
    ∀ a, GeneratedTenthFinalSourceCertificateIncomingEntry a := by
  intro a
  by_cases ha : a.val < 3840
  · let b : Fin 60 := ⟨a.val / 64, by omega⟩
    let u : Fin 64 := ⟨a.val % 64, Nat.mod_lt _ (by decide)⟩
    have he : generatedTenthFinalSourceCertificateIncomingLabel b u = a := by
      apply Fin.ext
      dsimp [generatedTenthFinalSourceCertificateIncomingLabel, b, u]
      omega
    simpa only [he] using h b u
  · let u : Fin 16 := ⟨a.val - 3840, by omega⟩
    have he : generatedTenthFinalSourceCertificateIncomingTail u = a := by
      apply Fin.ext
      dsimp [generatedTenthFinalSourceCertificateIncomingTail, u]
      omega
    simpa only [he] using ht u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
