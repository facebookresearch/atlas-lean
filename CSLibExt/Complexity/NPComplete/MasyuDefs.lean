/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MASYU: definitions

Source:
E. Friedman, "Pearl puzzles are NP-complete", manuscript, Stetson University (2002),
https://erich-friedman.github.io/papers/pearl/pearl.html;
H. Tang, "A framework for loop and path puzzle satisfiability NP-hardness results",
arXiv:2202.02046 (2022), Section 3.2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Masyu

/-- An instance: the grid row by row, each cell `0` (no pearl), `1` (white pearl) or `2` (black
pearl). -/
abbrev MasyuInstance := List (List ℕ)

/-- The number of rows `m`. -/
abbrev rows (i : MasyuInstance) : ℕ := i.length

/-- The number of columns `n` (the length of the first row). -/
abbrev cols (i : MasyuInstance) : ℕ := (i.headD []).length

/-- A cell `(row, column)` of the grid. -/
abbrev Cell (i : MasyuInstance) := Fin (rows i) × Fin (cols i)

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : MasyuInstance) : SimpleGraph (Cell i) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- The entry of cell `x`: `0` (no pearl), `1` (white pearl) or `2` (black pearl). -/
def cell (i : MasyuInstance) (x : Cell i) : ℕ :=
  (i.getD x.1 []).getD x.2 0

/-- Well-formedness: at least one row and one column, rows of equal length, and every entry at
most `2`. -/
def WellFormed (i : MasyuInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧ ∀ row ∈ i, ∀ e ∈ row, e ≤ 2

/-- The loop `c` turns at the cell `x`: two cells joined to `x` by edges of `c` differ in both
coordinates. -/
def IsTurn {i : MasyuInstance} {u : Cell i} (c : (Grid i).Walk u u) (x : Cell i) : Prop :=
  ∃ a b : Cell i, s(x, a) ∈ c.edges ∧ s(x, b) ∈ c.edges ∧ a.1 ≠ b.1 ∧ a.2 ≠ b.2

/-- The loop `c` goes straight through the cell `x`: two distinct cells joined to `x` by edges of
`c` lie in the same row or in the same column. -/
def IsStraight {i : MasyuInstance} {u : Cell i} (c : (Grid i).Walk u u) (x : Cell i) : Prop :=
  ∃ a b : Cell i, s(x, a) ∈ c.edges ∧ s(x, b) ∈ c.edges ∧ a ≠ b ∧ (a.1 = b.1 ∨ a.2 = b.2)

/-- The loop `c` satisfies the pearl rules. The cells immediately before and after `x` are the
cells `y` with `s(x, y)` an edge of `c`. -/
def Solves (i : MasyuInstance) {u : Cell i} (c : (Grid i).Walk u u) : Prop :=
  -- the loop passes through every pearl
  (∀ x, cell i x ≠ 0 → x ∈ c.support) ∧
  -- a black pearl: the loop turns at it and goes straight on the cells before and after it
  (∀ x, cell i x = 2 → IsTurn c x ∧ ∀ y, s(x, y) ∈ c.edges → IsStraight c y) ∧
  -- a white pearl: the loop goes straight through it and turns on a cell before or after it
  ∀ x, cell i x = 1 → IsStraight c x ∧ ∃ y, s(x, y) ∈ c.edges ∧ IsTurn c y

/-- Some cycle of the grid graph satisfies the pearl rules. -/
def MasyuFeasible (i : MasyuInstance) : Prop :=
  ∃ u, ∃ c : (Grid i).Walk u u, c.IsCycle ∧ Solves i c

open Classical in
/-- MASYU as a decision problem over bitstrings. -/
noncomputable def masyuDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MasyuInstance) x with
  | some i => decide (WellFormed i ∧ MasyuFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Masyu
