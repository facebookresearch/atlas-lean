/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WATER WALK: definitions

Source:
P. Eua-anant, P. Apinyanon, T. Jirachaisri, N. Ruangsuksriwong and S. Ruangwises,
"NP-completeness proofs of All or Nothing, Water Walk, and Remembered Length using the
T-metacell framework", arXiv:2510.21938 (2025), Section 2.2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WaterWalk

/-- An instance: the grid row by row, each cell `(water, number)` with number `0` for an
unnumbered cell. -/
abbrev WaterWalkInstance := List (List (Bool × ℕ))

/-- The number of rows. -/
def rows (i : WaterWalkInstance) : ℕ := i.length

/-- The number of columns (the length of the first row). -/
def cols (i : WaterWalkInstance) : ℕ := (i.headD []).length

/-- The entry `(water, number)` of cell `x`. -/
def cell (i : WaterWalkInstance) (x : Fin (rows i) × Fin (cols i)) : Bool × ℕ :=
  (i.getD x.1 []).getD x.2 (false, 0)

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : WaterWalkInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: at least one row and one column, rows of equal length, and numbers only on
ground cells. -/
def WellFormed (i : WaterWalkInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    ∀ row ∈ i, ∀ e ∈ row, e.1 = true → e.2 = 0

/-- The cycle `c` satisfies rules 1-3. -/
def Solves (i : WaterWalkInstance) {u : Fin (rows i) × Fin (cols i)} (c : (Grid i).Walk u u) :
    Prop :=
  -- 1. every numbered cell is on the loop
  (∀ x, 0 < (cell i x).2 → x ∈ c.support) ∧
  -- 2. the ground section through a numbered cell has exactly its number of cells
  (∀ j < c.length, 0 < (cell i (c.getVert j)).2 →
    ((∀ t < c.length, (cell i (c.getVert t)).1 = false) ∧
        (cell i (c.getVert j)).2 = c.length) ∨
      ∃ a < (cell i (c.getVert j)).2,
        (∀ t < (cell i (c.getVert j)).2,
          (cell i (c.getVert ((j + c.length - a + t) % c.length))).1 = false) ∧
        (cell i (c.getVert ((j + c.length - a - 1) % c.length))).1 = true ∧
        (cell i (c.getVert
          ((j + c.length - a + (cell i (c.getVert j)).2) % c.length))).1 = true) ∧
  -- 3. no three consecutive water cells
  ∀ j < c.length, ¬ ((cell i (c.getVert j)).1 = true ∧
    (cell i (c.getVert ((j + 1) % c.length))).1 = true ∧
    (cell i (c.getVert ((j + 2) % c.length))).1 = true)

/-- Some cycle of the grid graph satisfies the rules. -/
def WaterWalkFeasible (i : WaterWalkInstance) : Prop :=
  ∃ u, ∃ c : (Grid i).Walk u u, c.IsCycle ∧ Solves i c

open Classical in
/-- WATER WALK as a decision problem over bitstrings. -/
noncomputable def waterWalkDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WaterWalkInstance) x with
  | some i => decide (WellFormed i ∧ WaterWalkFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WaterWalk
