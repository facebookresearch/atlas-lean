/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHOCO BANANA: definitions

Source:
C. Iwamoto and T. Tokunaga, "Choco Banana is NP-complete", IEICE Transactions on Fundamentals
of Electronics, Communications and Computer Sciences E107-A(9) (2024), 1488-1491,
doi:10.1587/transfun.2023DML0001.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChocoBanana

/-- An instance: the rows of the grid, top to bottom; entry `0` is a cell without a number and
an entry `n ≥ 1` a cell containing the number `n`. -/
abbrev ChocoBananaInstance := List (List ℕ)

/-- The number of rows. -/
abbrev rows (i : ChocoBananaInstance) : ℕ := i.length

/-- The number of columns, the length of the first row. -/
abbrev cols (i : ChocoBananaInstance) : ℕ := (i.headD []).length

/-- The entry of the cell in row `p.1` and column `p.2` (`0`: no number). -/
def clue (i : ChocoBananaInstance) (p : Fin (rows i) × Fin (cols i)) : ℕ :=
  (i.getD p.1 []).getD p.2 0

/-- The grid graph: cells are adjacent when they share a side. -/
abbrev grid (h w : ℕ) : SimpleGraph (Fin h × Fin w) :=
  SimpleGraph.pathGraph h □ SimpleGraph.pathGraph w

/-- The grid edges between cells of the same color (`true`: black); its connected components
are the connected areas of the painting. -/
def areaGraph {h w : ℕ} (black : Fin h × Fin w → Bool) : SimpleGraph (Fin h × Fin w) :=
  grid h w ⊓ SimpleGraph.fromRel fun p q => black p = black q

/-- A set of cells is a rectangle area: all cells in rows `r₁ … r₂` and columns `c₁ … c₂`, for
some `r₁ ≤ r₂` and `c₁ ≤ c₂`. -/
def IsRectangle {h w : ℕ} (S : Set (Fin h × Fin w)) : Prop :=
  ∃ r₁ r₂ : Fin h, ∃ c₁ c₂ : Fin w, r₁ ≤ r₂ ∧ c₁ ≤ c₂ ∧
    S = {p | r₁ ≤ p.1 ∧ p.1 ≤ r₂ ∧ c₁ ≤ p.2 ∧ p.2 ≤ c₂}

/-- The connected area containing cell `p`. -/
def area {h w : ℕ} (black : Fin h × Fin w → Bool) (p : Fin h × Fin w) : Set (Fin h × Fin w) :=
  ((areaGraph black).connectedComponentMk p).supp

/-- Well-formedness of an instance: the grid has at least one row and one column, and every row
has the same length. -/
def WellFormed (i : ChocoBananaInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ ∀ row ∈ i, row.length = cols i

/-- Some painting satisfies the three rules: connected black areas are rectangles, connected
white areas are not, and every number is the size of its connected area. -/
def ChocoBananaFeasible (i : ChocoBananaInstance) : Prop :=
  ∃ black : Fin (rows i) × Fin (cols i) → Bool,
    (∀ p, black p = true → IsRectangle (area black p)) ∧
    (∀ p, black p = false → ¬ IsRectangle (area black p)) ∧
    ∀ p, clue i p ≠ 0 → (area black p).ncard = clue i p

open Classical in
/-- CHOCO BANANA as a decision problem over bitstrings. -/
noncomputable def chocoBananaDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChocoBananaInstance) x with
  | some i => decide (WellFormed i ∧ ChocoBananaFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChocoBanana
