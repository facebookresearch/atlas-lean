/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.RubiksSquareDefs

namespace MetaMathlibExt.Complexity.NPComplete.RubiksSquare

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : RubiksSquareInstance) :
    rubiksSquareDec (bitEncode i) = true ↔ WellFormed i ∧ RubiksSquareFeasible i := by
  simp [rubiksSquareDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : rubiksSquareDec [true] = false := by
  have h : bitDecode (α := RubiksSquareInstance) [true] = none := rfl
  simp [rubiksSquareDec, h]

/-- The `2 × 2` Rubik's Square after flipping row `0` of the canonical solved puzzle, with move
budget `k`: row `0` shows the bottom color `1` on top, and its `±x` side stickers have swapped
ends. -/
private abbrev flipped (k : ℕ) : RubiksSquareInstance :=
  (2, [[1, 1], [0, 0]], [[0, 0], [1, 1]], [3, 2], [2, 3], [4, 4], [5, 5], k)

/-- The coloring `flipped 1` is a configuration: one row flip of the canonical solved puzzle. -/
private theorem wellFormed_flipped : WellFormed (flipped 1) := by
  refine ⟨by decide, rfl, by decide, rfl, by decide, rfl, by decide, rfl, by decide, rfl,
    by decide, rfl, by decide, monoConfig 2 0 1 2 3 4 5, by simp [solvedPlacements],
    [Sum.inl ⟨0, by decide⟩], ?_⟩
  simp only [List.foldl_cons, List.foldl_nil, applyMove, flipRow, monoConfig, config,
    Config.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (funext x y; revert x y; decide)
    | (funext x; revert x; decide)

/-- Flipping row `0` again restores the solved puzzle, so one move suffices. -/
example : rubiksSquareDec (bitEncode (flipped 1)) = true := by
  refine (accepts_encoding _).2 ⟨wellFormed_flipped, [Sum.inl ⟨0, by decide⟩], le_rfl,
    0, 1, 2, 3, 4, 5, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [List.foldl_cons, List.foldl_nil, applyMove, flipRow, config] <;> decide

/-- With budget `0` the flipped puzzle stays unsolved: its top face shows colors `1` and `0`. -/
example : rubiksSquareDec (bitEncode (flipped 0)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, moves, hlen, cT, -, -, -, -, -, -, htop, -⟩ := (accepts_encoding _).1 h
  obtain rfl : moves = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
  have h0 := htop ⟨0, by decide⟩ ⟨0, by decide⟩
  have h1 := htop ⟨0, by decide⟩ ⟨1, by decide⟩
  have e := h0.trans h1.symm
  revert e
  decide

/-- A side list of the wrong length makes the instance malformed. -/
example : rubiksSquareDec (bitEncode ((1, [[0]], [[1]], [2, 2], [3], [4], [5], 0) :
    RubiksSquareInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd ((accepts_encoding _).1 h).1.2.2.2.2.2.1 (by decide)

end MetaMathlibExt.Complexity.NPComplete.RubiksSquare
