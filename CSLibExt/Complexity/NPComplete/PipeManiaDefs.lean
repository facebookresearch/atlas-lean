/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PIPE MANIA: definitions

Source:
G. Viglietta, "Gaming is a hard job, but someone has to do it!", Theory of Computing Systems
54(4) (2014), 595-621, doi:10.1007/s00224-013-9497-5, Section 3.7.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PipeMania

/-- An instance `(B, (r, c, d), N)`: the board row by row (`true` = obstacle), the source tile
`(r, c)` with outlet direction `d` (`0` up, `1` right, `2` down, `3` left), and the number `N`
of tiles to traverse. -/
abbrev PipeManiaInstance := List (List Bool) × (ℕ × ℕ × ℕ) × ℕ

/-- The number of rows. -/
def rows (i : PipeManiaInstance) : ℕ := i.1.length

/-- The number of columns (the length of the first row). -/
def cols (i : PipeManiaInstance) : ℕ := (i.1.headD []).length

/-- Tile `x` lies on the board and is not an obstacle. -/
def IsFree (i : PipeManiaInstance) (x : ℕ × ℕ) : Prop :=
  x.1 < rows i ∧ x.2 < cols i ∧ (i.1.getD x.1 []).getD x.2 true = false

/-- The source tile. -/
def source (i : PipeManiaInstance) : ℕ × ℕ := (i.2.1.1, i.2.1.2.1)

/-- The outlet direction of the source. -/
def outlet (i : PipeManiaInstance) : ℕ := i.2.1.2.2

/-- The required number of traversed tiles. -/
def target (i : PipeManiaInstance) : ℕ := i.2.2

/-- Tile `y` is the neighbor of tile `x` in direction `d`. -/
def Toward (x : ℕ × ℕ) (d : ℕ) (y : ℕ × ℕ) : Prop :=
  (d = 0 ∧ y.1 + 1 = x.1 ∧ y.2 = x.2) ∨ (d = 1 ∧ y.1 = x.1 ∧ y.2 = x.2 + 1) ∨
    (d = 2 ∧ y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (d = 3 ∧ y.1 = x.1 ∧ y.2 + 1 = x.2)

/-- Tiles `x` and `y` share a side. -/
def Adjacent (x y : ℕ × ℕ) : Prop := ∃ d < 4, Toward x d y

/-- The stream passes straight through tile `y`, entering from `x` and leaving to `z`. -/
def Straight (x y z : ℕ × ℕ) : Prop :=
  (x.1 = y.1 ∧ y.1 = z.1) ∨ (x.2 = y.2 ∧ y.2 = z.2)

/-- Well-formedness: at least one row and one column, rows of equal length, the source a free
tile, and the outlet a direction. -/
def WellFormed (i : PipeManiaInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.1, row.length = cols i) ∧ IsFree i (source i) ∧
    outlet i < 4

/-- `tile i w k` is the `k`-th tile of the stream's path `source :: w`: the source for
`k = 0`, the tile of traversal `k` for `1 ≤ k ≤ N`. -/
def tile (i : PipeManiaInstance) (w : List (ℕ × ℕ)) (k : ℕ) : ℕ × ℕ :=
  (source i :: w).getD k (0, 0)

/-- The route `w` (the tiles the stream traverses, in order) is realized by a placement of
pieces. Traversal `k` (`1 ≤ k ≤ N`) is of `tile i w k`, entered from `tile i w (k - 1)` and,
when `k < N`, left to `tile i w (k + 1)`. -/
def Route (i : PipeManiaInstance) (w : List (ℕ × ℕ)) : Prop :=
  w.length = target i ∧
  -- every traversed tile is free and not the source
  (∀ x ∈ w, IsFree i x ∧ x ≠ source i) ∧
  -- the stream leaves the source through its outlet
  (0 < target i → Toward (source i) (outlet i) (tile i w 1)) ∧
  -- consecutive tiles share a side
  (∀ k < target i, Adjacent (tile i w k) (tile i w (k + 1))) ∧
  -- no piece sends the stream back through the side it came in by (`k + 2 ≤ N`)
  (∀ k < target i - 1, tile i w k ≠ tile i w (k + 2)) ∧
  -- every tile is traversed at most twice
  (∀ x ∈ w, w.count x ≤ 2) ∧
  -- a tile traversed twice holds a cross: both passes straight, in perpendicular directions
  (∀ k ≤ target i, ∀ j < k, 1 ≤ j → tile i w j = tile i w k →
    Straight (tile i w (j - 1)) (tile i w j) (tile i w (j + 1)) ∧
    ((tile i w (j - 1)).1 = (tile i w j).1 ↔ (tile i w (k - 1)).1 ≠ (tile i w k).1) ∧
    (k < target i → Straight (tile i w (k - 1)) (tile i w k) (tile i w (k + 1))))

/-- Some placement of pieces makes the stream traverse `N` tiles. -/
def PipeManiaFeasible (i : PipeManiaInstance) : Prop :=
  ∃ w : List (ℕ × ℕ), Route i w

open Classical in
/-- PIPE MANIA as a decision problem over bitstrings. -/
noncomputable def pipeManiaDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PipeManiaInstance) x with
  | some i => decide (WellFormed i ∧ PipeManiaFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PipeMania
