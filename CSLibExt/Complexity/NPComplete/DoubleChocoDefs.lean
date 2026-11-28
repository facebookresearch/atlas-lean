/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOUBLE CHOCO: definitions

Source:
D. Đurić, "Double Choco is NP-complete", Master thesis, EPFL (2022), arXiv:2203.02815,
Chapter 1 and Chapter 4.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ChainedBlockDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DoubleChoco

open MetaMathlibExt.Complexity.NPComplete.ChainedBlock (SameShape coords)

/-- An instance: the board row by row, each cell `(color, number)` with color `0` (white) or
`1` (gray) and number `0` when the cell has no number. -/
abbrev DoubleChocoInstance := List (List (ℕ × ℕ))

/-- The number of rows. -/
def rows (i : DoubleChocoInstance) : ℕ := i.length

/-- The number of columns (the length of the first row). -/
def cols (i : DoubleChocoInstance) : ℕ := (i.headD []).length

/-- The entry `(color, number)` of cell `x`. -/
def cell (i : DoubleChocoInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ × ℕ :=
  (i.getD x.1 []).getD x.2 (0, 0)

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : DoubleChocoInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: at least one row and one column, rows of equal length, colors `0` or `1`,
and every number at most `mn / 2`. -/
def WellFormed (i : DoubleChocoInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    ∀ row ∈ i, ∀ e ∈ row, e.1 ≤ 1 ∧ 2 * e.2 ≤ rows i * cols i

/-- The block with label `k` of the labeling `blk` satisfies the rules: its white area, its gray
area and the block itself are connected, the two areas have the same shape, and every number
in the block is the size of its white area. -/
def GoodBlock (i : DoubleChocoInstance) (blk : Fin (rows i) × Fin (cols i) → ℕ) (k : ℕ) :
    Prop :=
  ((Grid i).induce {x | blk x = k ∧ (cell i x).1 = 0}).Connected ∧
    ((Grid i).induce {x | blk x = k ∧ (cell i x).1 = 1}).Connected ∧
    ((Grid i).induce {x | blk x = k}).Connected ∧
    SameShape (coords {x | blk x = k ∧ (cell i x).1 = 0})
      (coords {x | blk x = k ∧ (cell i x).1 = 1}) ∧
    ∀ x, blk x = k → (cell i x).2 ≠ 0 →
      {y | blk y = k ∧ (cell i y).1 = 0}.ncard = (cell i x).2

/-- Some division of the board into blocks satisfies the rules. -/
def DoubleChocoFeasible (i : DoubleChocoInstance) : Prop :=
  ∃ blk : Fin (rows i) × Fin (cols i) → ℕ, ∀ x, GoodBlock i blk (blk x)

open Classical in
/-- DOUBLE CHOCO as a decision problem over bitstrings. -/
noncomputable def doubleChocoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := DoubleChocoInstance) x with
  | some i => decide (WellFormed i ∧ DoubleChocoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DoubleChoco
