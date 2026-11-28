/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# YAJILIN: definitions

Source:
A. Ishibashi, Y. Sato and S. Iwata, "NP-completeness of two pencil puzzles: Yajilin and Country
Road", Utilitas Mathematica 88 (2012), 237-246;
H. Tang, "A framework for loop and path puzzle satisfiability NP-hardness results",
arXiv:2202.02046 (2022), Section 3.3.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Yajilin

/-- An instance: the grid row by row, each cell `(flag, k, d)`: `flag = 0` for an ordinary cell,
`flag = 1` for a clue cell with number `k` and arrow `d` (`0` up, `1` down, `2` left, `3`
right). -/
abbrev YajilinInstance := List (List (ℕ × ℕ × ℕ))

/-- The number of rows `m`. -/
abbrev rows (i : YajilinInstance) : ℕ := i.length

/-- The number of columns `n` (the length of the first row). -/
abbrev cols (i : YajilinInstance) : ℕ := (i.headD []).length

/-- A cell `(row, column)` of the grid. -/
abbrev Cell (i : YajilinInstance) := Fin (rows i) × Fin (cols i)

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : YajilinInstance) : SimpleGraph (Cell i) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- The entry `(flag, k, d)` of cell `x`. -/
def cell (i : YajilinInstance) (x : Cell i) : ℕ × ℕ × ℕ :=
  (i.getD x.1 []).getD x.2 (0, 0, 0)

/-- Cell `x` is a clue (grey) cell. -/
abbrev IsClue (i : YajilinInstance) (x : Cell i) : Prop := (cell i x).1 = 1

/-- Cell `y` lies in direction `d` from cell `x`: in the same column above `x` (`d = 0`) or
below it (`d = 1`), or in the same row left of `x` (`d = 2`) or right of it (`d = 3`). -/
abbrev InDirection {i : YajilinInstance} (d : ℕ) (x y : Cell i) : Prop :=
  (d = 0 ∧ y.2 = x.2 ∧ y.1 < x.1) ∨ (d = 1 ∧ y.2 = x.2 ∧ x.1 < y.1) ∨
    (d = 2 ∧ y.1 = x.1 ∧ y.2 < x.2) ∨ (d = 3 ∧ y.1 = x.1 ∧ x.2 < y.2)

/-- Well-formedness: at least one row and one column, rows of equal length, and every entry
either an ordinary cell `(0, 0, 0)` or a clue `(1, k, d)` with `d ≤ 3`. -/
def WellFormed (i : YajilinInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    ∀ row ∈ i, ∀ e ∈ row, (e.1 = 0 ∧ e.2.1 = 0 ∧ e.2.2 = 0) ∨ (e.1 = 1 ∧ e.2.2 ≤ 3)

/-- Cell `y` is shaded for the loop `c`: an ordinary cell not passed through by the loop. -/
abbrev IsShaded (i : YajilinInstance) {u : Cell i} (c : (Grid i).Walk u u) (y : Cell i) :
    Prop :=
  ¬ IsClue i y ∧ y ∉ c.support

/-- The loop `c` satisfies the rules of Yajilin. -/
def Solves (i : YajilinInstance) {u : Cell i} (c : (Grid i).Walk u u) : Prop :=
  -- the grey (clue) cells are not part of the loop
  (∀ x, IsClue i x → x ∉ c.support) ∧
  -- no two shaded cells are adjacent
  (∀ x y, (Grid i).Adj x y → ¬ (IsShaded i c x ∧ IsShaded i c y)) ∧
  -- a clue `(1, k, d)`: there are `k` shaded cells in direction `d`
  ∀ x, IsClue i x →
    (Finset.univ.filter fun y => InDirection (cell i x).2.2 x y ∧ IsShaded i c y).card =
      (cell i x).2.1

/-- Some cycle of the grid graph satisfies the rules. -/
def YajilinFeasible (i : YajilinInstance) : Prop :=
  ∃ u, ∃ c : (Grid i).Walk u u, c.IsCycle ∧ Solves i c

open Classical in
/-- YAJILIN as a decision problem over bitstrings. -/
noncomputable def yajilinDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := YajilinInstance) x with
  | some i => decide (WellFormed i ∧ YajilinFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Yajilin
