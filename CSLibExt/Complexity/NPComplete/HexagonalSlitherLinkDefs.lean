/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HEXAGONAL SLITHER LINK: definitions

Source:
J. Kölker, "Selected Slither Link variants are NP-complete", Journal of Information
Processing 20(3) (2012), 709-712, doi:10.2197/ipsjjip.20.709, Theorem 3.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HexagonalSlitherLink

/-- An instance: the clue grid, column by column from the left; entry `r` of column `c` is the
clue of hexagon `(c, r)`, `0` for no clue and `v + 1` for clue value `v`. The raw type is any
list of columns of any lengths. The rectangle is fixed by the number of columns (`width`) and the
length of the first column (`height`); `WellFormed` asks every column to have that length. -/
abbrev HexagonalSlitherLinkInstance := List (List ℕ)

/-- The number of columns `w`. -/
def width (i : HexagonalSlitherLinkInstance) : ℕ := i.length

/-- The number of hexagons `h` in each column (the length of the first column). -/
def height (i : HexagonalSlitherLinkInstance) : ℕ := (i.headD []).length

/-- The clue entry of hexagon `(c, r)`. -/
def clue (i : HexagonalSlitherLinkInstance) (c r : ℕ) : ℕ := (i.getD c []).getD r 0

/-- The six sides of hexagon `(c, r)`, clockwise from its top side, with `y₀ = 2r + c % 2` the
height of its top side; its corners are `(c, y₀)`, `(c + 1, y₀)`, `(c + 1, y₀ + 1)`,
`(c + 1, y₀ + 2)`, `(c, y₀ + 2)` and `(c, y₀ + 1)`. -/
def sides (c r : ℕ) : List (Sym2 (ℕ × ℕ)) :=
  let y₀ := 2 * r + c % 2
  [s((c, y₀), (c + 1, y₀)), s((c + 1, y₀), (c + 1, y₀ + 1)),
    s((c + 1, y₀ + 1), (c + 1, y₀ + 2)), s((c + 1, y₀ + 2), (c, y₀ + 2)),
    s((c, y₀ + 2), (c, y₀ + 1)), s((c, y₀ + 1), (c, y₀))]

/-- The hexagonal grid with `w` columns of `h` hexagons, as a graph on all of `ℕ × ℕ`: two points
are adjacent when they are the ends of a side of one of its hexagons. Every pair of naturals is a
vertex; a point that is not a corner of a grid hexagon is isolated. -/
def Graph (i : HexagonalSlitherLinkInstance) : SimpleGraph (ℕ × ℕ) :=
  SimpleGraph.fromRel fun p q => ∃ c < width i, ∃ r < height i, s(p, q) ∈ sides c r

/-- Well-formedness: `w ≥ 1` columns, each of `h ≥ 1` hexagons. -/
def WellFormed (i : HexagonalSlitherLinkInstance) : Prop :=
  0 < width i ∧ 0 < height i ∧ ∀ col ∈ i, col.length = height i

/-- Some cycle `cyc` of the grid has, for every clue hexagon, exactly as many of the hexagon's
sides among its edges as the clue value. Only the hexagons `(c, r)` with `c < width` and
`r < height` are read, the rectangle fixed by the number of columns and the length of the first
column: entries of a longer column beyond `height` are ignored, and a missing entry of a shorter
column reads as no clue. -/
def HexagonalSlitherLinkFeasible (i : HexagonalSlitherLinkInstance) : Prop :=
  ∃ u, ∃ cyc : (Graph i).Walk u u, cyc.IsCycle ∧
    ∀ c < width i, ∀ r < height i, 0 < clue i c r →
      (sides c r).countP (· ∈ cyc.edges) + 1 = clue i c r

open Classical in
/-- HEXAGONAL SLITHER LINK as a decision problem over bitstrings. -/
noncomputable def hexagonalSlitherLinkDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HexagonalSlitherLinkInstance) x with
  | some i => decide (WellFormed i ∧ HexagonalSlitherLinkFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HexagonalSlitherLink
