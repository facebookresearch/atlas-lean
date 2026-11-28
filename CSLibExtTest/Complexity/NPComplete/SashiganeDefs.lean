/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SashiganeDefs

namespace MetaMathlibExt.Complexity.NPComplete.Sashigane

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SashiganeInstance) :
    sashiganeDec (bitEncode i) = true ↔ WellFormed i ∧ SashiganeFeasible i := by
  simp [sashiganeDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : sashiganeDec [true] = false := by
  have h : bitDecode (α := SashiganeInstance) [true] = none := rfl
  simp [sashiganeDec, h]

/-- A `2 × 3` grid with a white circle `3` in the top-left cell and a downward arrow in the
top-right cell. -/
private abbrev grid23 : SashiganeInstance :=
  [[(1, 3), (0, 0), (2, 1)], [(0, 0), (0, 0), (0, 0)]]

/-- The L with corner `(0, 0)` and arms ending at `(1, 0)` and `(0, 1)`. -/
private abbrev blockA : Block grid23 :=
  ((⟨0, by decide⟩, ⟨0, by decide⟩), (⟨1, by decide⟩, ⟨0, by decide⟩),
    (⟨0, by decide⟩, ⟨1, by decide⟩))

/-- The L with corner `(1, 2)` and arms ending at `(0, 2)` and `(1, 1)`. -/
private abbrev blockB : Block grid23 :=
  ((⟨1, by decide⟩, ⟨2, by decide⟩), (⟨0, by decide⟩, ⟨2, by decide⟩),
    (⟨1, by decide⟩, ⟨1, by decide⟩))

/-- Cells with coordinate sum at most `1` go to `blockA`, the others to `blockB`. -/
private def assign (x : Cell grid23) : Block grid23 :=
  if (x.1 : ℕ) + (x.2 : ℕ) ≤ 1 then blockA else blockB

/-- The two Ls `blockA` and `blockB` divide the grid: the circle is the corner of the
three-cell `blockA`, and the arrow is an end of `blockB` pointing down to its corner. -/
example : sashiganeDec (bitEncode grid23) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, assign, ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨?_, ?_, ?_⟩
    · revert x; unfold IsL; decide
    · revert x; unfold InBlock; decide
    · revert x; unfold InBlock; decide
  · decide
  · unfold blockSize; decide
  · unfold ArrowOK; decide

/-- An empty `2 × 2` grid. -/
private abbrev grid22 : SashiganeInstance := [[(0, 0), (0, 0)], [(0, 0), (0, 0)]]

/-- Every L in the `2 × 2` grid misses exactly one cell. -/
private theorem misses (b : Block grid22) (hb : IsL b) :
    ∃ m, ¬ InBlock b m ∧ ∀ y, y ≠ m → InBlock b y := by
  revert b
  unfold IsL InBlock
  decide

/-- Two cells of the `2 × 2` grid leave a third one. -/
private theorem third (m m' : Cell grid22) : ∃ y, y ≠ m ∧ y ≠ m' := by
  revert m m'
  decide

/-- The empty `2 × 2` grid cannot be divided into Ls: the L of the cell `(0, 0)` misses one cell
`z`, the L of `z` misses a cell other than `z`, and a third cell lies in both Ls, which forces
them to be the same L. -/
example : sashiganeDec (bitEncode grid22) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, B, hB, -⟩ := (accepts_encoding _).1 h
  let x : Cell grid22 := (⟨0, by decide⟩, ⟨0, by decide⟩)
  obtain ⟨hLx, -, hx⟩ := hB x
  obtain ⟨z, hz, hzall⟩ := misses _ hLx
  obtain ⟨hLz, hzz, hzsame⟩ := hB z
  obtain ⟨m', hm', hm'all⟩ := misses _ hLz
  obtain ⟨y, hyz, hym'⟩ := third z m'
  have e : B x = B z := (hx y (hzall y hyz)).symm.trans (hzsame y (hm'all y hym'))
  exact hz (e ▸ hzz)

/-- An arrow direction above `3` makes the grid malformed. -/
example : sashiganeDec (bitEncode ([[(2, 4)]] : SashiganeInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := ((accepts_encoding _).1 h).1.2.2.2 [(2, 4)] (by simp) (2, 4) (by simp)
  simp at this

end MetaMathlibExt.Complexity.NPComplete.Sashigane
