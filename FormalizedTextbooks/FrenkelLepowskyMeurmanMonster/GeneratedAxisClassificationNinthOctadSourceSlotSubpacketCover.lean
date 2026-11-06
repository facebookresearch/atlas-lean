/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotPacketCover

/-! Eight-address subpackets cover each original finite address packet exactly. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- An eight-address interval within an original64-address packet. -/
def generatedNinthSlotSubpacketIndex64 (b : Fin 8)
    (m : Fin (if b.val = 7 then 8 else 8)) : Fin 64 :=
  ⟨8 * b.val + m.val, by
    have hm := m.isLt
    split_ifs at hm <;> omega⟩

/-- Exhaustive eight-address intervals prove a property on the complete64-address packet. -/
theorem generatedNinth_slot_subpacket_cover_64 (P : Fin 64 → Prop)
    (h : ∀ b : Fin 8, ∀ m : Fin (if b.val = 7 then 8 else 8),
      P (generatedNinthSlotSubpacketIndex64 b m)) : ∀ k : Fin 64, P k := by
  intro k
  let b : Fin 8 := ⟨k.val / 8, by omega⟩
  let m : Fin (if b.val = 7 then 8 else 8) := ⟨k.val % 8, by
    dsimp only [b]
    split_ifs <;> omega⟩
  have hi : generatedNinthSlotSubpacketIndex64 b m = k := by
    apply Fin.ext
    change 8 * b.val + m.val = k.val
    dsimp only [b, m]
    omega
  rw [← hi]
  exact h b m

/-- An eight-address interval within an original55-address packet. -/
def generatedNinthSlotSubpacketIndex55 (b : Fin 7)
    (m : Fin (if b.val = 6 then 7 else 8)) : Fin 55 :=
  ⟨8 * b.val + m.val, by
    have hm := m.isLt
    split_ifs at hm <;> omega⟩

/-- Exhaustive eight-address intervals prove a property on the complete55-address packet. -/
theorem generatedNinth_slot_subpacket_cover_55 (P : Fin 55 → Prop)
    (h : ∀ b : Fin 7, ∀ m : Fin (if b.val = 6 then 7 else 8),
      P (generatedNinthSlotSubpacketIndex55 b m)) : ∀ k : Fin 55, P k := by
  intro k
  let b : Fin 7 := ⟨k.val / 8, by omega⟩
  let m : Fin (if b.val = 6 then 7 else 8) := ⟨k.val % 8, by
    dsimp only [b]
    split_ifs <;> omega⟩
  have hi : generatedNinthSlotSubpacketIndex55 b m = k := by
    apply Fin.ext
    change 8 * b.val + m.val = k.val
    dsimp only [b, m]
    omega
  rw [← hi]
  exact h b m

/-- An eight-address interval within an original256-address packet. -/
def generatedNinthSlotSubpacketIndex256 (b : Fin 32)
    (m : Fin (if b.val = 31 then 8 else 8)) : Fin 256 :=
  ⟨8 * b.val + m.val, by
    have hm := m.isLt
    split_ifs at hm <;> omega⟩

/-- Exhaustive eight-address intervals prove a property on the complete256-address packet. -/
theorem generatedNinth_slot_subpacket_cover_256 (P : Fin 256 → Prop)
    (h : ∀ b : Fin 32, ∀ m : Fin (if b.val = 31 then 8 else 8),
      P (generatedNinthSlotSubpacketIndex256 b m)) : ∀ k : Fin 256, P k := by
  intro k
  let b : Fin 32 := ⟨k.val / 8, by omega⟩
  let m : Fin (if b.val = 31 then 8 else 8) := ⟨k.val % 8, by
    dsimp only [b]
    split_ifs <;> omega⟩
  have hi : generatedNinthSlotSubpacketIndex256 b m = k := by
    apply Fin.ext
    change 8 * b.val + m.val = k.val
    dsimp only [b, m]
    omega
  rw [← hi]
  exact h b m

/-- An eight-address interval within an original40-address packet. -/
def generatedNinthSlotSubpacketIndex40 (b : Fin 5)
    (m : Fin (if b.val = 4 then 8 else 8)) : Fin 40 :=
  ⟨8 * b.val + m.val, by
    have hm := m.isLt
    split_ifs at hm <;> omega⟩

/-- Exhaustive eight-address intervals prove a property on the complete40-address packet. -/
theorem generatedNinth_slot_subpacket_cover_40 (P : Fin 40 → Prop)
    (h : ∀ b : Fin 5, ∀ m : Fin (if b.val = 4 then 8 else 8),
      P (generatedNinthSlotSubpacketIndex40 b m)) : ∀ k : Fin 40, P k := by
  intro k
  let b : Fin 5 := ⟨k.val / 8, by omega⟩
  let m : Fin (if b.val = 4 then 8 else 8) := ⟨k.val % 8, by
    dsimp only [b]
    split_ifs <;> omega⟩
  have hi : generatedNinthSlotSubpacketIndex40 b m = k := by
    apply Fin.ext
    change 8 * b.val + m.val = k.val
    dsimp only [b, m]
    omega
  rw [← hi]
  exact h b m

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
