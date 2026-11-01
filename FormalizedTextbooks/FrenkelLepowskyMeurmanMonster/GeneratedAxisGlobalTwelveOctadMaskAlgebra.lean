/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskBytes
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskBounds
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskFinite

/-! Exact algebra of compact column-XOR mask maps, used by the octad-family binary forest.
Composition, identity, bounded decoding and the split into low and high coordinate blocks are
proved for arbitrary column lists; no finite certificate is assumed here. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The zero mask is sent to zero by every column list. -/
theorem generatedAxisGlobalTwelveOctadRows_zero (rows : List (ℕ × ℕ)) :
    generatedAxisGlobalMaskRowsAction rows 0 = 0 := by
  induction rows with
  | nil => rfl
  | cons p rows ih =>
      rcases p with ⟨i, c⟩
      simp [generatedAxisGlobalMaskRowsAction, ih]

/-- Composition of two column-XOR maps is the column-XOR map of the transported columns. -/
theorem generatedAxisGlobalTwelveOctadRows_comp (r₁ r₂ : List (ℕ × ℕ)) (b : ℕ) :
    generatedAxisGlobalMaskRowsAction r₁ (generatedAxisGlobalMaskRowsAction r₂ b) =
      generatedAxisGlobalMaskRowsAction
        (r₂.map (fun p => (p.1, generatedAxisGlobalMaskRowsAction r₁ p.2))) b := by
  induction r₂ with
  | nil => exact generatedAxisGlobalTwelveOctadRows_zero r₁
  | cons p rows ih =>
      rcases p with ⟨i, c⟩
      cases h : b.testBit i
      · simp only [generatedAxisGlobalMaskRowsAction, h, Bool.false_eq_true, ↓reduceIte,
          List.map_cons]
        exact ih
      · simp only [generatedAxisGlobalMaskRowsAction, h, ↓reduceIte, List.map_cons]
        rw [Nat.xor_eq, generatedAxisGlobalMaskRowsAction_xor, ih]
        rfl

/-- A column list is bounded by `2 ^ n` on a mask whose used columns are bounded. -/
theorem generatedAxisGlobalTwelveOctadRows_lt_of_used (n : ℕ) (rows : List (ℕ × ℕ)) (b : ℕ)
    (h : ∀ p ∈ rows, b.testBit p.1 = true → p.2 < 2 ^ n) :
    generatedAxisGlobalMaskRowsAction rows b < 2 ^ n := by
  induction rows with
  | nil => exact Nat.two_pow_pos n
  | cons p rows ih =>
      rcases p with ⟨i, c⟩
      have hr : ∀ q ∈ rows, b.testBit q.1 = true → q.2 < 2 ^ n := by
        intro q hq
        exact h q (by simp [hq])
      cases hb : b.testBit i
      · simpa [generatedAxisGlobalMaskRowsAction, hb] using ih hr
      · simp only [generatedAxisGlobalMaskRowsAction, hb, ↓reduceIte]
        exact Nat.xor_lt_two_pow (h (i, c) (by simp) hb) (ih hr)

/-- Masks below `2 ^ 24` are determined by their genuine decoded coordinate vectors. -/
theorem generatedAxisGlobalTwelveOctadMask_eq_of_decode {a b : ℕ} (ha : a < 2 ^ 24)
    (hb : b < 2 ^ 24)
    (h : monsterCo1GeometryBinaryMaskDecode (n := 24) a =
      monsterCo1GeometryBinaryMaskDecode (n := 24) b) : a = b := by
  have := generatedAxisGlobalMaskDecodeFinite_injective 24
    (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) h
  exact congrArg Fin.val this

/-- The unit columns give the identity column-XOR map on all bounded masks. -/
theorem generatedAxisGlobalTwelveOctadRows_unit (b : ℕ) (hb : b < 2 ^ 24) :
    generatedAxisGlobalMaskRowsAction
      (List.ofFn (fun j : Fin 24 => (j.val, 2 ^ j.val))) b = b := by
  apply generatedAxisGlobalTwelveOctadMask_eq_of_decode
  · apply generatedAxisGlobalMaskRowsAction_lt
    intro p hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    exact Nat.pow_lt_pow_right (by norm_num) j.isLt
  · exact hb
  · rw [generatedAxisGlobalMaskRowsAction_ofFn (fun j : Fin 24 => 2 ^ j.val),
      generatedAxisGlobalMaskColumnAction_decode]
    have hm : generatedAxisGlobalMaskColumnMatrix (fun j : Fin 24 => 2 ^ j.val) = 1 := by
      ext i j
      change monsterCo1GeometryBinaryMaskDecode (2 ^ j.val) i = _
      rw [generatedAxisGlobalMaskDecode_two_pow]
      simp [Matrix.one_apply, Pi.single_apply]
    rw [hm, Matrix.one_mulVec]

/-- A row list built from bounded columns maps every mask below `2 ^ 24`. -/
theorem generatedAxisGlobalTwelveOctadRows_ofFn_lt (a : Fin 24 → ℕ)
    (ha : ∀ j, a j < 2 ^ 24) (b : ℕ) :
    generatedAxisGlobalMaskRowsAction (List.ofFn (fun j : Fin 24 => (j.val, a j))) b <
      2 ^ 24 := by
  apply generatedAxisGlobalMaskRowsAction_lt
  intro p hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  exact ha j

/-- The genuine decoded action of a row list built from columns is the column matrix action. -/
theorem generatedAxisGlobalTwelveOctadRows_ofFn_decode (a : Fin 24 → ℕ) (b : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 24)
        (generatedAxisGlobalMaskRowsAction (List.ofFn (fun j : Fin 24 => (j.val, a j))) b) =
      generatedAxisGlobalMaskColumnMatrix a *ᵥ monsterCo1GeometryBinaryMaskDecode b := by
  rw [generatedAxisGlobalMaskRowsAction_ofFn, generatedAxisGlobalMaskColumnAction_decode]

/-- Splitting a bounded mask into its low sixteen and high eight coordinates is exact. -/
theorem generatedAxisGlobalTwelveOctadMask_split16 (c : ℕ) :
    c = (c % 65536) ^^^ ((c >>> 16) <<< 16) := by
  have h := generatedAxisGlobalMask_split c 16
  rw [Nat.shiftRight_eq_div_pow]
  norm_num only [show (2 : ℕ) ^ 16 = 65536 by norm_num] at h ⊢
  exact h

/-- A low block below `2 ^ 16` does not affect the high coordinates of an XOR. -/
theorem generatedAxisGlobalTwelveOctadMask_xor_high (a b : ℕ) (ha : a < 2 ^ 16) :
    (a ^^^ b) >>> 16 = b >>> 16 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_xor,
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num)
      (by omega : 16 ≤ 16 + i)))]
  simp

/-- High coordinates of an image depend only on the high block when low columns stay low. -/
theorem generatedAxisGlobalTwelveOctadRows_high (rows : List (ℕ × ℕ))
    (hlow : ∀ p ∈ rows, p.1 < 16 → p.2 < 2 ^ 16) (c : ℕ) :
    generatedAxisGlobalMaskRowsAction rows c >>> 16 =
      generatedAxisGlobalMaskRowsAction rows ((c >>> 16) <<< 16) >>> 16 := by
  conv_lhs => rw [generatedAxisGlobalTwelveOctadMask_split16 c]
  rw [generatedAxisGlobalMaskRowsAction_xor]
  apply generatedAxisGlobalTwelveOctadMask_xor_high
  apply generatedAxisGlobalTwelveOctadRows_lt_of_used
  intro p hp hbit
  apply hlow p hp
  by_contra hge
  have : (c % 65536).testBit p.1 = false := by
    apply Nat.testBit_eq_false_of_lt
    calc c % 65536 < 65536 := Nat.mod_lt _ (by norm_num)
      _ = 2 ^ 16 := by norm_num
      _ ≤ 2 ^ p.1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [this] at hbit
  exact Bool.false_ne_true hbit

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
