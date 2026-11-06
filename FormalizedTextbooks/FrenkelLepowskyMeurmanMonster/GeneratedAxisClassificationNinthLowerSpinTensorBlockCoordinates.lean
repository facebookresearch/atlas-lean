/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorInputData

/-! Exact source-label blocks and Fourier XORs select complete packed source rows
before finite integer replay. The complete original packed coordinates are retained. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A complete source spin label in a fixed 256-coordinate row. -/
def generatedNinthLowerSpinTensorBlockIndex (b : Fin 16) (u : Fin 256) : Fin 4096 :=
  ⟨b.val * 256 + u.val, by omega⟩

private theorem bit_bound (k : Fin 12) : 2 ^ k.val < 4096 := by
  simpa only [show 2 ^ 12 = 4096 by decide] using
    Nat.pow_lt_pow_right (by decide : 1 < 2) k.isLt

/-- The exact source row after one original Fourier bit is toggled. -/
def generatedNinthLowerSpinTensorBlockXorHigh (k : Fin 12) (b : Fin 16) : Fin 16 :=
  ⟨Nat.xor b.val (2 ^ k.val / 256), by
    have h : 2 ^ k.val / 256 < 16 := by have := bit_bound k; omega
    change Nat.xor b.val (2 ^ k.val / 256) < 2 ^ 4
    exact Nat.xor_lt_two_pow b.isLt h⟩

/-- The exact offset in a source row after one original Fourier bit is toggled. -/
def generatedNinthLowerSpinTensorBlockXorLow (k : Fin 12) (u : Fin 256) : Fin 256 :=
  ⟨Nat.xor u.val (2 ^ k.val % 256), by
    change Nat.xor u.val (2 ^ k.val % 256) < 2 ^ 8
    exact Nat.xor_lt_two_pow u.isLt (Nat.mod_lt _ (by decide))⟩

/-- The entire original twelve-bit source label splits exactly after every Fourier XOR. -/
theorem generatedNinth_lower_spin_tensor_block_xor (k : Fin 12) (b : Fin 16) (u : Fin 256) :
    (⟨(Nat.xor (generatedNinthLowerSpinTensorBlockIndex b u).val (2 ^ k.val)) % 4096,
      Nat.mod_lt _ (by decide)⟩ : Fin 4096) =
      generatedNinthLowerSpinTensorBlockIndex
        (generatedNinthLowerSpinTensorBlockXorHigh k b)
        (generatedNinthLowerSpinTensorBlockXorLow k u) := by
  apply Fin.ext
  have hn : b.val * 256 + u.val < 4096 := by omega
  have hx : Nat.xor (b.val * 256 + u.val) (2 ^ k.val) < 4096 := by
    change Nat.xor (b.val * 256 + u.val) (2 ^ k.val) < 2 ^ 12
    exact Nat.xor_lt_two_pow hn (bit_bound k)
  have hb : (b.val * 256 + u.val) / 256 = b.val := by omega
  have hu : (b.val * 256 + u.val) % 256 = u.val := by omega
  have hd := (Nat.xor_div_two_pow (a := b.val * 256 + u.val)
    (b := 2 ^ k.val) (n := 8))
  have hm := (Nat.xor_mod_two_pow (a := b.val * 256 + u.val)
    (b := 2 ^ k.val) (n := 8))
  change (Nat.xor (b.val * 256 + u.val) (2 ^ k.val)) / 256 = _ at hd
  change (Nat.xor (b.val * 256 + u.val) (2 ^ k.val)) % 256 = _ at hm
  rw [hb] at hd
  rw [hu] at hm
  change Nat.xor (b.val * 256 + u.val) (2 ^ k.val) / 256 =
    Nat.xor b.val (2 ^ k.val / 256) at hd
  change Nat.xor (b.val * 256 + u.val) (2 ^ k.val) % 256 =
    Nat.xor u.val (2 ^ k.val % 256) at hm
  dsimp only [generatedNinthLowerSpinTensorBlockIndex,
    generatedNinthLowerSpinTensorBlockXorHigh, generatedNinthLowerSpinTensorBlockXorLow]
  rw [Nat.mod_eq_of_lt hx]
  have hh := Nat.mod_add_div (Nat.xor (b.val * 256 + u.val) (2 ^ k.val)) 256
  rw [hd, hm] at hh
  omega

/-- Every packed source coordinate uses exactly its original row, word and signed slot. -/
theorem generatedNinth_lower_spin_tensor_packed_coordinate_block
    (words : Fin 16 → Fin 16 → ℕ) (b : Fin 16) (u : Fin 256) :
    generatedNinthLowerSpinTensorPackedCoordinate words
      (generatedNinthLowerSpinTensorBlockIndex b u) =
        generatedNinthLowerSpinTensorDecode
          (words b ⟨u.val / 16, by omega⟩) (u.val % 16) := by
  have hb : (b.val * 256 + u.val) / 256 = b.val := by omega
  have hm : (b.val * 256 + u.val) / 16 % 16 = u.val / 16 := by omega
  have hl : (b.val * 256 + u.val) % 16 = u.val % 16 := by omega
  dsimp only [generatedNinthLowerSpinTensorPackedCoordinate,
    generatedNinthLowerSpinTensorBlockIndex]
  simp only [hb, hm, hl]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
