/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HITORI: definitions

Source:
R. A. Hearn and E. D. Demaine, *Games, Puzzles, and Computation*, A K Peters (2009),
Section 9.2 "Hitori", pp. 112-115, doi:10.1201/b10581;
puzzle rules: M. L. Pacheco, F. Somenzi, D. Srinivas and A. Trivedi, "Explaining Hitori
puzzles: neurosymbolic proof staging for sequential decisions", arXiv:2508.14294 (2025),
Section 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Hitori

/-- An instance: the grid row by row, each entry the number in the cell. -/
abbrev HitoriInstance := List (List ℕ)

/-- The number of rows `m`. -/
abbrev rows (i : HitoriInstance) : ℕ := i.length

/-- The number of columns `n` (the length of the first row). -/
abbrev cols (i : HitoriInstance) : ℕ := (i.headD []).length

/-- A cell `(row, column)` of the grid. -/
abbrev Cell (i : HitoriInstance) := Fin (rows i) × Fin (cols i)

/-- The grid graph on the cells: cells sharing an edge are adjacent. -/
abbrev Grid (i : HitoriInstance) : SimpleGraph (Cell i) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- The number in cell `x`. -/
def cell (i : HitoriInstance) (x : Cell i) : ℕ :=
  (i.getD x.1 []).getD x.2 0

/-- Well-formedness: at least one row and one column, and rows of equal length. -/
def WellFormed (i : HitoriInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ ∀ row ∈ i, row.length = cols i

/-- The shading `s` (`true` = shaded) satisfies the three conditions. -/
def Solves (i : HitoriInstance) (s : Cell i → Bool) : Prop :=
  -- 1. uniqueness: no number appears more than once unshaded in any row or column
  (∀ x y, x ≠ y → (x.1 = y.1 ∨ x.2 = y.2) → cell i x = cell i y →
    s x = true ∨ s y = true) ∧
  -- 2. separation: shaded cells do not share an edge
  (∀ x y, (Grid i).Adj x y → ¬ (s x = true ∧ s y = true)) ∧
  -- 3. connection: the unshaded cells form an edge-connected region
  ((Grid i).induce {x | s x = false}).Connected

/-- Some shading satisfies the conditions. -/
def HitoriFeasible (i : HitoriInstance) : Prop :=
  ∃ s : Cell i → Bool, Solves i s

open Classical in
/-- HITORI as a decision problem over bitstrings. -/
noncomputable def hitoriDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := HitoriInstance) x with
  | some i => decide (WellFormed i ∧ HitoriFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Hitori
