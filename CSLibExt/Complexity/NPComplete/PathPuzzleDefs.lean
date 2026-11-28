/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH PUZZLE (complete row and column information): definitions

Source:
J. Bosboom, E. D. Demaine, M. L. Demaine, A. Hesterberg, R. Kimball and J. Kopinsky, "Path
puzzles: discrete tomography with a path constraint is hard", Graphs and Combinatorics 36
(2020), 251-267, doi:10.1007/s00373-019-02092-5.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathPuzzle

/-- A door: the boundary cell `(row, column)` and the side it opens to (`0` top, `1` bottom,
`2` left, `3` right). -/
abbrev Door := (ℕ × ℕ) × ℕ

/-- An instance: row clues `R`, column clues `C`, and the two doors. -/
abbrev PathPuzzleInstance := List ℕ × List ℕ × Door × Door

/-- A cell `(row, column)` of the grid. -/
abbrev Cell (i : PathPuzzleInstance) := Fin i.1.length × Fin i.2.1.length

/-- Orthogonal adjacency of cells: the grid graph, the box product of two path graphs. -/
abbrev gridGraph (i : PathPuzzleInstance) : SimpleGraph (Cell i) :=
  SimpleGraph.pathGraph i.1.length □ SimpleGraph.pathGraph i.2.1.length

/-- A door of an `h × w` grid: its cell is in the grid and lies on the side it opens to. -/
def IsDoor (h w : ℕ) (d : Door) : Prop :=
  d.1.1 < h ∧ d.1.2 < w ∧
    ((d.2 = 0 ∧ d.1.1 = 0) ∨ (d.2 = 1 ∧ d.1.1 + 1 = h) ∨ (d.2 = 2 ∧ d.1.2 = 0) ∨
      (d.2 = 3 ∧ d.1.2 + 1 = w))

/-- Well-formedness of an instance: two different doors on the boundary of the grid. -/
def WellFormed (i : PathPuzzleInstance) : Prop :=
  IsDoor i.1.length i.2.1.length i.2.2.1 ∧ IsDoor i.1.length i.2.1.length i.2.2.2 ∧
    i.2.2.1 ≠ i.2.2.2

/-- The puzzle has a solution: a non-intersecting path in the grid graph from the cell of the
first door to the cell of the second door that passes through exactly `R[r]` cells of each row
`r` and exactly `C[c]` cells of each column `c`. -/
def PathPuzzleFeasible (i : PathPuzzleInstance) : Prop :=
  ∃ a b : Cell i, ((a.1 : ℕ), (a.2 : ℕ)) = i.2.2.1.1 ∧ ((b.1 : ℕ), (b.2 : ℕ)) = i.2.2.2.1 ∧
    ∃ W : (gridGraph i).Walk a b, W.IsPath ∧
      (∀ r : Fin i.1.length, W.support.countP (fun v => v.1 = r) = i.1[r]) ∧
      ∀ c : Fin i.2.1.length, W.support.countP (fun v => v.2 = c) = i.2.1[c]

open Classical in
/-- PATH PUZZLE as a decision problem over bitstrings. -/
noncomputable def pathPuzzleDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathPuzzleInstance) x with
  | some i => decide (WellFormed i ∧ PathPuzzleFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathPuzzle
