/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KUROTTO: definitions

Source:
C. Iwamoto and T. Ibusuki, "Polynomial-time reductions from 3SAT to Kurotto and Juosan
puzzles", IEICE Transactions on Information and Systems E103-D(3) (2020), 500-505,
doi:10.1587/transinf.2019FCP0004.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Kurotto

/-- An instance: the rows of the grid, top to bottom; the entry of a cell is
`(circle, numbered, number)`. -/
abbrev KurottoInstance := List (List (Bool × Bool × ℕ))

/-- The number of rows. -/
abbrev rows (i : KurottoInstance) : ℕ := i.length

/-- The number of columns, the length of the first row. -/
abbrev cols (i : KurottoInstance) : ℕ := (i.headD []).length

/-- The cells of the grid. -/
abbrev Cell (i : KurottoInstance) := Fin (rows i) × Fin (cols i)

/-- The entry `(circle, numbered, number)` of the cell in row `p.1` and column `p.2`. -/
def entry (i : KurottoInstance) (p : Cell i) : Bool × Bool × ℕ :=
  (i.getD p.1 []).getD p.2 (false, false, 0)

/-- The grid graph: cells are adjacent when they share a side. -/
abbrev grid (h w : ℕ) : SimpleGraph (Fin h × Fin w) :=
  SimpleGraph.pathGraph h □ SimpleGraph.pathGraph w

/-- Well-formedness of an instance: at least one row and one column, every row of the same
length, only cells with circles contain numbers, and a cell without a number stores `0`. -/
def WellFormed (i : KurottoInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    ∀ row ∈ i, ∀ e ∈ row, (e.2.1 = true → e.1 = true) ∧ (e.2.1 = false → e.2.2 = 0)

/-- The black cells extending from the cell `p` when the cells of `B` are black: the black cells
joined by a path of black cells to a black cell adjacent to `p`. -/
def extending (i : KurottoInstance) (B : Set (Cell i)) (p : Cell i) : Set (Cell i) :=
  {q | ∃ hq : q ∈ B, ∃ r, (grid (rows i) (cols i)).Adj p r ∧
    ∃ hr : r ∈ B, ((grid (rows i) (cols i)).induce B).Reachable ⟨r, hr⟩ ⟨q, hq⟩}

/-- Coloring the cells of `B` black satisfies the rules: no cell with a circle is black, and the
number of black cells extending from each numbered circle is its number. -/
def Solves (i : KurottoInstance) (B : Set (Cell i)) : Prop :=
  (∀ p ∈ B, (entry i p).1 = false) ∧
    ∀ p, (entry i p).1 = true → (entry i p).2.1 = true →
      (extending i B p).ncard = (entry i p).2.2

/-- Some coloring satisfies the rules. -/
def KurottoFeasible (i : KurottoInstance) : Prop :=
  ∃ B : Set (Cell i), Solves i B

open Classical in
/-- KUROTTO as a decision problem over bitstrings. -/
noncomputable def kurottoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KurottoInstance) x with
  | some i => decide (WellFormed i ∧ KurottoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Kurotto
