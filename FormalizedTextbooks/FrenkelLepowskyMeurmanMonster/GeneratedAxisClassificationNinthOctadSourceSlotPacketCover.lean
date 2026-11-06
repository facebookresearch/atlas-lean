/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotsData

/-! Exact consecutive finite intervals cover all octad and chronological source addresses. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Consecutive64-address octad packets with a restricted final packet. -/
def generatedNinthOctadPacketIndex (b : Fin 12)
    (m : Fin (if b.val = 11 then 55 else 64)) : Fin 759 :=
  ⟨64 * b.val + m.val, by
    have hm := m.isLt
    split_ifs at hm <;> omega⟩

/-- Complete consecutive packet coverage implies a property at every actual octad address. -/
theorem generatedNinth_octad_packet_cover (P : Fin 759 → Prop)
    (h : ∀ b : Fin 12, ∀ m : Fin (if b.val = 11 then 55 else 64),
      P (generatedNinthOctadPacketIndex b m)) : ∀ k : Fin 759, P k := by
  intro k
  let b : Fin 12 := ⟨k.val / 64, by omega⟩
  let m : Fin (if b.val = 11 then 55 else 64) := ⟨k.val % 64, by
    dsimp only [b]
    split_ifs <;> omega⟩
  have hi : generatedNinthOctadPacketIndex b m = k := by
    apply Fin.ext
    change 64 * b.val + m.val = k.val
    dsimp only [b, m]
    omega
  rw [← hi]
  exact h b m

/-- Consecutive256-address source packets with a restricted final packet. -/
def generatedNinthSourcePacketIndex (b : Fin 17)
    (m : Fin (if b.val = 16 then 40 else 256)) : Fin 4136 :=
  ⟨256 * b.val + m.val, by
    have hm := m.isLt
    split_ifs at hm <;> omega⟩

/-- Complete consecutive packet coverage implies a property at every actual source address. -/
theorem generatedNinth_source_packet_cover (P : Fin 4136 → Prop)
    (h : ∀ b : Fin 17, ∀ m : Fin (if b.val = 16 then 40 else 256),
      P (generatedNinthSourcePacketIndex b m)) : ∀ k : Fin 4136, P k := by
  intro k
  let b : Fin 17 := ⟨k.val / 256, by omega⟩
  let m : Fin (if b.val = 16 then 40 else 256) := ⟨k.val % 256, by
    dsimp only [b]
    split_ifs <;> omega⟩
  have hi : generatedNinthSourcePacketIndex b m = k := by
    apply Fin.ext
    change 256 * b.val + m.val = k.val
    dsimp only [b, m]
    omega
  rw [← hi]
  exact h b m

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
