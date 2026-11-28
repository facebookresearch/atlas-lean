/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.RubiksCubeDefs

namespace MetaMathlibExt.Complexity.NPComplete.RubiksCube

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : RubiksCubeInstance) :
    rubiksCubeDec (bitEncode i) = true ↔ WellFormed i ∧ RubiksCubeFeasible i := by
  simp [rubiksCubeDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : rubiksCubeDec [true] = false := by
  have h : bitDecode (α := RubiksCubeInstance) [true] = none := rfl
  simp [rubiksCubeDec, h]

/-- The `2 × 2 × 2` cube after one quarter turn of the slice `x = 0` (move `(0, 0, 0)`) from the
canonical solved cube, with move budget `k`. -/
private abbrev turned (k : ℕ) : RubiksCubeInstance :=
  (2, [[[0, 0], [0, 0]], [[1, 1], [1, 1]], [[4, 2], [4, 2]], [[5, 3], [5, 3]],
    [[3, 3], [4, 4]], [[2, 2], [5, 5]]], k)

/-- The coloring `turned 1` is a configuration: one quarter turn of the canonical solved cube. -/
private theorem wellFormed_turned : WellFormed (turned 1) := by
  refine ⟨by decide, rfl, by decide, [(0, ⟨0, by decide⟩, 0)], ?_⟩
  funext a s u v
  revert a s u v
  decide

/-- Three more quarter turns of the same slice (move `(0, 0, 2)`) solve the cube in one move. -/
example : rubiksCubeDec (bitEncode (turned 1)) = true := by
  refine (accepts_encoding _).2 ⟨wellFormed_turned, [(0, ⟨0, by decide⟩, 2)], le_rfl,
    fun a s => 2 * (a : ℕ) + if s then 0 else 1, by decide, ?_⟩
  decide

/-- With budget `0` the turned cube stays unsolved: its `+y` face shows colors `4` and `2`. -/
example : rubiksCubeDec (bitEncode (turned 0)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, moves, hlen, col, -, hcol⟩ := (accepts_encoding _).1 h
  obtain rfl : moves = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
  have h0 := hcol 1 true ⟨0, by decide⟩ ⟨0, by decide⟩
  have h1 := hcol 1 true ⟨0, by decide⟩ ⟨1, by decide⟩
  have e := h0.trans h1.symm
  revert e
  decide

/-- A sticker color `6` makes the instance malformed. -/
example : rubiksCubeDec (bitEncode ((1, [[[6]], [[1]], [[2]], [[3]], [[4]], [[5]]], 0) :
    RubiksCubeInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := (((accepts_encoding _).1 h).1.2.2.1 [[6]] (by simp)).2 [6] (by simp)
  exact absurd (this.2 6 (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.RubiksCube
