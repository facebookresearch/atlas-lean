/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SASHIGANE: definitions

Source:
C. Iwamoto and T. Ide, "Computational complexity of Nurimisaki and Sashigane", IEICE
Transactions on Fundamentals of Electronics, Communications and Computer Sciences E103-A(10)
(2020), 1183-1192, doi:10.1587/transfun.2019DMP0002;
puzzle rules: Nikoli Co., Ltd., "Sashigane" (Japanese rules page),
https://www.nikoli.co.jp/ja/puzzles/sashigane/.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Nat.Dist

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Sashigane

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

end MetaMathlibExt.Complexity.NPComplete.Sashigane
