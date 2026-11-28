/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TetravexDefs

namespace MetaMathlibExt.Complexity.NPComplete.Tetravex

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : TetravexInstance) :
    tetravexDec (bitEncode i) = true ↔ WellFormed i ∧ TetravexFeasible i := by
  simp [tetravexDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : tetravexDec [true] = false := by
  have h : bitDecode (α := TetravexInstance) [true] = none := rfl
  simp [tetravexDec, h]

/-- Four tiles fill the two-by-two board when tile `x + 2 y` sits at `(x, y)`: every shared
edge carries matching labels. -/
example :
    tetravexDec
      (bitEncode ((2, [(0, 1, 2, 0), (0, 0, 3, 1), (2, 4, 0, 0), (3, 0, 0, 4)]) :
        TetravexInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨rfl, fun x y => x + 2 * y, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    simp at hx hy ⊢
    omega
  · intro x hx y hy x' hx' y' hy' h
    simp at hx hy hx' hy' h
    omega
  · intro x y hx hy
    simp at hx hy
    obtain rfl : x = 0 := by omega
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> rfl
  · intro x y hx hy
    simp at hx hy
    obtain rfl : y = 0 := by omega
    rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> rfl

/-- Four copies of a tile with right label `1` and left label `0` cannot fill the
two-by-two board: whatever sits at `(0, 0)` and `(1, 0)` disagrees on their shared edge. -/
example :
    tetravexDec
      (bitEncode ((2, [(0, 1, 0, 0), (0, 1, 0, 0), (0, 1, 0, 0), (0, 1, 0, 0)]) :
        TetravexInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, f, hrange, -, hhoriz, -⟩
  have hall : ∀ k < 4,
      [(0, 1, 0, 0), (0, 1, 0, 0), (0, 1, 0, 0), (0, 1, 0, 0)].getD k (0, 0, 0, 0) =
        (0, 1, 0, 0) := by decide
  have h00 := hrange 0 (by simp) 0 (by simp)
  have h10 := hrange 1 (by simp) 0 (by simp)
  have h := hhoriz 0 0 (by simp) (by simp)
  simp only [List.length_cons, List.length_nil] at h00 h10
  simp only [hall _ h00, hall _ h10] at h
  exact absurd h (by decide)

/-- The rejected instance is well formed: it has four tiles for four cells. -/
example : WellFormed ((2, [(0, 1, 0, 0), (0, 1, 0, 0), (0, 1, 0, 0), (0, 1, 0, 0)]) :
    TetravexInstance) := rfl

/-- Three tiles do not fill a two-by-two board. -/
example :
    tetravexDec
      (bitEncode ((2, [(0, 1, 2, 0), (0, 0, 3, 1), (2, 4, 0, 0)]) : TetravexInstance)) =
        false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨h, -⟩
  revert h
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.Tetravex
