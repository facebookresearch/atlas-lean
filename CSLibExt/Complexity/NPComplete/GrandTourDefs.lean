/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAND TOUR: definitions

Source:
N. Kiatchaipipat and S. Ruangwises, "NP-completeness proofs of puzzles using the T-metacell
framework", arXiv:2508.11570 (2025), Section 2.1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GrandTour

/-- An instance: the grid row by row, each point carrying the flags `(right, down)`: whether the
edge to its right neighbour and the edge to its lower neighbour are forced. -/
abbrev GrandTourInstance := List (List (Bool × Bool))

/-- The number of rows. -/
def rows (i : GrandTourInstance) : ℕ := i.length

/-- The number of columns (the length of the first row). -/
def cols (i : GrandTourInstance) : ℕ := (i.headD []).length

/-- The flags `(right, down)` of the point `x`. -/
def flags (i : GrandTourInstance) (x : Fin (rows i) × Fin (cols i)) : Bool × Bool :=
  (i.getD x.1 []).getD x.2 (false, false)

/-- The grid graph on the points: points one step apart horizontally or vertically are
adjacent. -/
abbrev Grid (i : GrandTourInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: at least one row and one column, rows of equal length, no forced edge to
the right of the last column, and no forced edge below the last row. -/
def WellFormed (i : GrandTourInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    (∀ row ∈ i, (row.getLastD (false, false)).1 = false) ∧
    ∀ e ∈ i.getLastD [], e.2 = false

/-- The edge from `x` to `y` is forced: `y` is the right neighbour of `x` and `x` has its
`right` flag, or `y` is the lower neighbour of `x` and `x` has its `down` flag. -/
def Forced (i : GrandTourInstance) (x y : Fin (rows i) × Fin (cols i)) : Prop :=
  (x.1 = y.1 ∧ (x.2 : ℕ) + 1 = y.2 ∧ (flags i x).1 = true) ∨
    (x.2 = y.2 ∧ (x.1 : ℕ) + 1 = y.1 ∧ (flags i x).2 = true)

/-- Some Hamiltonian cycle of the grid graph uses every forced edge. -/
def GrandTourFeasible (i : GrandTourInstance) : Prop :=
  ∃ u, ∃ c : (Grid i).Walk u u, c.IsHamiltonianCycle ∧
    ∀ x y, Forced i x y → s(x, y) ∈ c.edges

open Classical in
/-- GRAND TOUR as a decision problem over bitstrings. -/
noncomputable def grandTourDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GrandTourInstance) x with
  | some i => decide (WellFormed i ∧ GrandTourFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GrandTour
