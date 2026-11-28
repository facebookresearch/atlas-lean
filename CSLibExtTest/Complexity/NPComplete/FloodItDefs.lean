/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.FloodItDefs

namespace MetaMathlibExt.Complexity.NPComplete.FloodIt

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (c : ℕ) (i : FloodItInstance) :
    floodItDec c (bitEncode i) = true ↔ WellFormed c i ∧ FloodItFeasible c i := by
  simp [floodItDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding, for every number of colours. -/
example (c : ℕ) : floodItDec c [true] = false := by
  have h : bitDecode (α := FloodItInstance) [true] = none := rfl
  simp [floodItDec, h]

/-- A `2 × 2` board with the top left tile of colour `0` and the other three of colour `1`, and
move bound `k`. -/
private abbrev board₂ (k : ℕ) : FloodItInstance := (2, [0, 1, 1, 1], k)

/-- The top left tile. -/
private abbrev corner : Fin 2 × Fin 2 := (0, 0)

/-- The top left tile has no neighbour of its own colour, so its region is the tile alone. -/
private theorem region_iff (k : ℕ) (x : Fin 2 × Fin 2) :
    Region (board (board₂ k)) x ↔ x = corner := by
  have other : ∀ v : Fin 2 × Fin 2, v ≠ corner → board (board₂ k) v = 1 := by
    show ∀ v : Fin 2 × Fin 2, v ≠ corner → [0, 1, 1, 1].getD (v.1 * 2 + v.2) 0 = 1
    decide
  constructor
  · rintro ⟨t, ht₁, ht₂, ⟨p⟩⟩
    obtain rfl : t = corner := Prod.ext (Fin.ext ht₁) (Fin.ext ht₂)
    cases p with
    | nil => rfl
    | cons h _ =>
      obtain ⟨hne, hr⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
      have hv := other _ hne.symm
      have h₀ : board (board₂ k) corner = 0 := rfl
      rcases hr with ⟨-, hc⟩ | ⟨-, hc⟩ <;> omega
  · rintro rfl
    exact ⟨corner, rfl, rfl, .refl _⟩

/-- With two or more colours and one move, flooding with colour `1` makes the board
monochromatic. -/
example (c : ℕ) (hc : 2 ≤ c) : floodItDec c (bitEncode (board₂ 1)) = true := by
  have other : ∀ v : Fin 2 × Fin 2, v ≠ corner → board (board₂ 1) v = 1 := by decide
  have all_one : ∀ x, [1].foldl flood (board (board₂ 1)) x = 1 := fun x => by
    simp only [List.foldl_cons, List.foldl_nil, flood]
    by_cases hx : x = corner
    · simp [(region_iff 1 x).2 hx]
    · simp [mt (region_iff 1 x).1 hx, other x hx]
  refine (accepts_encoding _ _).2 ⟨⟨by decide, rfl, ?_⟩, [1], le_rfl, ?_, ?_⟩
  · intro a ha
    simp at ha
    omega
  · intro a ha
    simp at ha
    omega
  · intro x y
    rw [all_one, all_one]

/-- With no moves allowed the board keeps both colours. -/
example : floodItDec 2 (bitEncode (board₂ 0)) = false := by
  have h : ¬ FloodItFeasible 2 (board₂ 0) := by
    rintro ⟨moves, hlen, -, hall⟩
    obtain rfl : moves = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
    exact absurd (hall corner (0, 1)) (by decide)
  simpa [floodItDec, bitDecode_bitEncode] using fun _ => h

/-- With a single colour the same board is malformed: its tiles of colour `1` are out of range.
-/
example : floodItDec 1 (bitEncode (board₂ 1)) = false := by
  have h : ¬ WellFormed 1 (board₂ 1) := by
    unfold WellFormed
    decide
  simp [floodItDec, bitDecode_bitEncode, h]

end MetaMathlibExt.Complexity.NPComplete.FloodIt
