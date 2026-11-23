/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SASHIGANE is NP-complete

Source:
C. Iwamoto and T. Ide, "Computational complexity of Nurimisaki and Sashigane", IEICE
Transactions on Fundamentals of Electronics, Communications and Computer Sciences E103-A(10)
(2020), 1183-1192, doi:10.1587/transfun.2019DMP0002;
puzzle rules: Nikoli Co., Ltd., "Sashigane" (Japanese rules page),
https://www.nikoli.co.jp/ja/puzzles/sashigane/.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Nat.Dist

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Sashigane

/-!
# SASHIGANE is NP-complete

Sashigane (Nikoli) is played on a rectangular grid in which some cells hold a white circle,
possibly with a number, or an arrow. Nikoli's rules (translated):
1. Draw lines along the dotted grid lines to divide the board into L-shaped blocks of width one
   cell. No block may have a shape other than an L.
2. A cell with a white circle is always the corner (the bend) of its L-shaped block.
3. The number in a white circle is the number of cells of the block containing it. For a white
   circle without a number, the size of the block is not known.
4. A cell with an arrow is always an end of its block, and the corner of that block lies in the
   direction the arrow points.
5. A block may contain any number, from `0` to `3`, of symbols (white circles and arrows).

INSTANCE: a rectangular grid with some cells holding a white circle (with or without a number)
or an arrow. QUESTION: can the grid be divided into blocks satisfying rules 1-5? (Iwamoto and
Ide 2020 prove this NP-complete for Nikoli's Sashigane; their full text was not available, so
the rules follow Nikoli's rules page.)

The grid is given row by row: entry `c` of row `r` is `(kind, value)` for cell `(r, c)`: kind
`0` (empty, value `0`), kind `1` (white circle; value `0` for no number, otherwise its number),
or kind `2` (arrow; value `0`, `1`, `2`, `3` for an arrow pointing up, down, left, right; row
indices grow downward). `WellFormed` requires at least one row and one column, rows of equal
length, and these kinds and values.

An L-shaped block of width one is given by its corner `o`, the end `v` of its vertical arm (in
the column of `o`, in another row) and the end `h` of its horizontal arm (in the row of `o`, in
another column); its cells are the cells of the two segments from `o` to `v` and from `o` to
`h`, and it has `|v - o| + |h - o| + 1` cells. A division of the grid into such blocks is a map
`B` sending each cell `x` to the block containing it: `x` lies in `B x`, and every cell `y` of
`B x` has `B y = B x`. Rule 5 imposes no condition.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the grid row by row, each cell `(kind, value)`. -/
abbrev SashiganeInstance := List (List (ℕ × ℕ))

/-- The number of rows. -/
def rows (i : SashiganeInstance) : ℕ := i.length

/-- The number of columns (the length of the first row). -/
def cols (i : SashiganeInstance) : ℕ := (i.headD []).length

/-- A cell of the grid. -/
abbrev Cell (i : SashiganeInstance) := Fin (rows i) × Fin (cols i)

/-- The entry `(kind, value)` of cell `x`. -/
def clue (i : SashiganeInstance) (x : Cell i) : ℕ × ℕ := (i.getD x.1 []).getD x.2 (0, 0)

/-- Well-formedness: at least one row and one column, rows of equal length, and every entry
empty `(0, 0)`, a white circle `(1, v)`, or an arrow `(2, d)` with `d ≤ 3`. -/
def WellFormed (i : SashiganeInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    ∀ row ∈ i, ∀ e ∈ row, e = (0, 0) ∨ e.1 = 1 ∨ (e.1 = 2 ∧ e.2 ≤ 3)

/-- A block `(o, v, h)`: corner `o`, vertical arm end `v`, horizontal arm end `h`. -/
abbrev Block (i : SashiganeInstance) := Cell i × Cell i × Cell i

/-- The block is an L of width one: `v` is in the column of `o` and another row, and `h` is in
the row of `o` and another column. -/
def IsL {i : SashiganeInstance} (b : Block i) : Prop :=
  b.2.1.2 = b.1.2 ∧ b.2.1.1 ≠ b.1.1 ∧ b.2.2.1 = b.1.1 ∧ b.2.2.2 ≠ b.1.2

/-- Cell `y` lies in the block: on the vertical segment from `o` to `v` or on the horizontal
segment from `o` to `h`. -/
def InBlock {i : SashiganeInstance} (b : Block i) (y : Cell i) : Prop :=
  (y.2 = b.1.2 ∧ min b.1.1 b.2.1.1 ≤ y.1 ∧ y.1 ≤ max b.1.1 b.2.1.1) ∨
    (y.1 = b.1.1 ∧ min b.1.2 b.2.2.2 ≤ y.2 ∧ y.2 ≤ max b.1.2 b.2.2.2)

/-- The number of cells of the block. -/
def blockSize {i : SashiganeInstance} (b : Block i) : ℕ :=
  Nat.dist b.1.1 b.2.1.1 + Nat.dist b.1.2 b.2.2.2 + 1

/-- The arrow at `x` pointing in direction `d` (up, down, left, right) satisfies rule 4 in block
`b`: `x` is an end of `b` and the corner lies in direction `d` from `x`. -/
def ArrowOK {i : SashiganeInstance} (b : Block i) (x : Cell i) (d : ℕ) : Prop :=
  (x = b.2.1 ∧ ((d = 0 ∧ b.1.1 < x.1) ∨ (d = 1 ∧ x.1 < b.1.1))) ∨
    (x = b.2.2 ∧ ((d = 2 ∧ b.1.2 < x.2) ∨ (d = 3 ∧ x.2 < b.1.2)))

/-- The map `B` divides the grid into L-shaped blocks of width one satisfying rules 2-4. -/
def Solves (i : SashiganeInstance) (B : Cell i → Block i) : Prop :=
  (∀ x, IsL (B x) ∧ InBlock (B x) x ∧ ∀ y, InBlock (B x) y → B y = B x) ∧
  (∀ x, (clue i x).1 = 1 → (B x).1 = x) ∧
  (∀ x, (clue i x).1 = 1 → (clue i x).2 ≠ 0 → blockSize (B x) = (clue i x).2) ∧
  ∀ x, (clue i x).1 = 2 → ArrowOK (B x) x (clue i x).2

/-- Some division of the grid into blocks satisfies the rules. -/
def SashiganeFeasible (i : SashiganeInstance) : Prop :=
  ∃ B : Cell i → Block i, Solves i B

open Classical in
/-- SASHIGANE as a decision problem over bitstrings. -/
noncomputable def sashiganeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SashiganeInstance) x with
  | some i => decide (WellFormed i ∧ SashiganeFeasible i)
  | none => false

/-- **SASHIGANE is NP-complete.** Source: Iwamoto and Ide (2020). -/
public theorem_wanted sashigane_npComplete :
    sashiganeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sashiganeDec

end MetaMathlibExt.Complexity.NPComplete.Sashigane
