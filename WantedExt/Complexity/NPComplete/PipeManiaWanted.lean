/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PIPE MANIA is NP-complete

Source:
G. Viglietta, "Gaming is a hard job, but someone has to do it!", Theory of Computing Systems
54(4) (2014), 595-621, doi:10.1007/s00224-013-9497-5, Section 3.7.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PipeMania

/-!
# PIPE MANIA is NP-complete

Viglietta (2014), Section 3.7, "Pipe Mania (The Assembly Line, 1989) is NP-complete": "in this
puzzle game a long-enough pipe has to be constructed out of several pieces, randomly presented
in a queue, starting from a given source location. After a timer expires, a stream of water
starts flowing from the source into the pipes, and the game is won if and only if the stream
traverses a given number of tiles before spilling out. Since the player can keep constructing
pipes on the same tile, 'overwriting' the previous pieces until he gets the piece that he wants,
he may indeed shape the pipe as he pleases, if the initial timer lasts long enough. Some
obstacles are also present in each level, such as fire hydrants, on which pipes cannot be
built." The reduction lets the pipe cover most tiles twice using cross-shaped pieces, and
measures the pipe's length counting such a tile twice.

INSTANCE: a rectangular board of tiles, some of them obstacles; a source tile with the direction
of its outlet; a number `N`.
QUESTION: can pipe pieces be placed on free tiles so that the stream from the source traverses
`N` tiles before spilling out?

Representation. The board is given row by row (`true` = obstacle), so the instance size is
proportional to its area plus the binary length of `N`. Tiles are pairs `(row, column)`;
directions are `0` up, `1` right, `2` down, `3` left. The pieces are Pipe Mania's straight
pieces, the four elbows, and the cross; each piece other than the cross joins two different
sides of its tile, and the cross joins left with right and top with bottom. Since the player
shapes the pipe freely, a placement is described by the stream's route: the list of the `N`
tiles it traverses after leaving the source, in order, a tile traversed twice listed twice.
Such a list is realized by a placement exactly when the first tile is the source's neighbor in
the outlet direction; consecutive tiles share a side; every listed tile is a free tile of the
board other than the source; the stream never leaves a tile through the side it entered by (no
piece joins a side to itself); and every tile is traversed at most once, or twice through a
cross: both passes straight, one horizontal and one vertical (the second pass may be the last
traversal, whose exit side is then the side opposite its entry). The tiles after the last
traversal play no role, as the stream may spill out there.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PIPE MANIA is NP-complete.** Source: Viglietta (2014), Section 3.7. -/
public theorem_wanted pipeMania_npComplete :
    pipeManiaDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pipeManiaDec

end MetaMathlibExt.Complexity.NPComplete.PipeMania
