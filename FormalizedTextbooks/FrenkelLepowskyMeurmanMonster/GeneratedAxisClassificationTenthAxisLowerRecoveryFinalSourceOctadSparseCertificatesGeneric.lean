/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceOctadSparseGeneric

/-! Complete original incoming octad source-coordinate certificate domains. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The original octad index recovered from a complete source address. -/
def generatedTenthFinalSourceOctadSparseOctad (a : Fin 48576) : Fin 759 :=
  ⟨a.val / 64, by omega⟩

/-- The original within-octad coordinate recovered from the same source address. -/
def generatedTenthFinalSourceOctadSparseCoordinate (a : Fin 48576) : Fin 64 :=
  ⟨a.val % 64, Nat.mod_lt _ (by decide)⟩

/-- Exact source equality covers every original octad coefficient, including all zeros. -/
def GeneratedTenthFinalSourceOctadSparseCertificate (a : Fin 48576) : Prop :=
  generatedTenthFinalSourceCertificateIncomingC
      (Sum.inr (Sum.inl (generatedTenthFinalSourceOctadSparseOctad a,
        generatedTenthFinalSourceOctadSparseCoordinate a))) =
    generatedTenthFinalSourceOctadSparseCoefficient
      (generatedTenthFinalSourceOctadSparseOctad a)
      (generatedTenthFinalSourceOctadSparseCoordinate a)

/-- Complete 256-coordinate source packets preserve the original octad address order. -/
def generatedTenthFinalSourceOctadSparsePacketAddress (b : Fin 189) (u : Fin 256) : Fin 48576 :=
  ⟨256 * b.val + u.val, by omega⟩

/-- The exact 192-coordinate tail retains the final three original octads. -/
def generatedTenthFinalSourceOctadSparseTailAddress (u : Fin 192) : Fin 48576 :=
  ⟨48384 + u.val, by omega⟩

/-- All packets and the exact tail cover all 759 by 64 original source coordinates. -/
theorem generatedTenth_final_source_octad_sparse_source_of_packets
    (h : ∀ b u, GeneratedTenthFinalSourceOctadSparseCertificate
      (generatedTenthFinalSourceOctadSparsePacketAddress b u))
    (ht : ∀ u, GeneratedTenthFinalSourceOctadSparseCertificate
      (generatedTenthFinalSourceOctadSparseTailAddress u)) :
    ∀ a, GeneratedTenthFinalSourceOctadSparseCertificate a := by
  intro a
  by_cases ha : a.val < 48384
  · let b : Fin 189 := ⟨a.val / 256, by omega⟩
    let u : Fin 256 := ⟨a.val % 256, Nat.mod_lt _ (by decide)⟩
    have he : generatedTenthFinalSourceOctadSparsePacketAddress b u = a := by
      apply Fin.ext
      dsimp [generatedTenthFinalSourceOctadSparsePacketAddress, b, u]
      omega
    simpa only [he] using h b u
  · let u : Fin 192 := ⟨a.val - 48384, by omega⟩
    have he : generatedTenthFinalSourceOctadSparseTailAddress u = a := by
      apply Fin.ext
      dsimp [generatedTenthFinalSourceOctadSparseTailAddress, u]
      omega
    simpa only [he] using ht u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
