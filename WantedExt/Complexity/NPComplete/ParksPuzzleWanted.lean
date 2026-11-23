/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# (c, r)-TREE PARKS PUZZLE is NP-complete

Source:
I. Minevich, G. Cunningham, K. A. Karan and J. V. Gyllinsky, "Parks: A Doubly Infinite Family
of NP-Complete Puzzles and Generalizations of A002464", arXiv:2411.02251 (2024), Definition 1,
Section IV and Theorem 2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Data.Finset.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.BattleshipsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ParksPuzzle

/-!
# (c, r)-TREE PARKS PUZZLE is NP-complete

Minevich, Cunningham, Karan and Gyllinsky (2024), Definition 1: for positive integers `c` and
`r`, a `(c, r)`-tree Parks puzzle is an `m × n` board with `m` regions called parks. The goal is
to place trees in the squares of the grid (at most one in any square) such that
* each column contains exactly `c` trees,
* each row contains exactly `r` trees,
* each park contains exactly `r` trees, and
* no two trees are on squares that are adjacent to one another (not even diagonally).

INSTANCE: an `m × n` board whose squares are divided into `m` parks.
QUESTION: can trees be placed so that the four conditions hold?

Theorem 2 of the paper: for any positive integers `c` and `r`, the family of `(c, r)`-tree Parks
puzzles is NP-complete. Accordingly `c` and `r` are fixed parameters of the decision problem
`parksPuzzleDec c r`, and the theorem below is stated for every `c, r ≥ 1`.

The board is given row by row: entry `j` of row `k` is the park of the square in row `k` and
column `j`; the parks are `0, …, m - 1`, where `m` is the number of rows. `WellFormed` requires
`m, n ≥ 1`, rows of equal length, park indices below `m`, and every park nonempty (the board
has `m` regions). Parks need not be contiguous: the paper's decision problem "says nothing
about the parks being contiguous regions" (Section V), its NP membership argument "assumes
nothing about the contiguity of the parks" (Section IV), and its hardness proof uses contiguous
parks, so the theorem holds with or without contiguity. Every solvable instance satisfies the
paper's equation (1), `c n = r m`; it is not imposed.

A placement is a finite set `T` of squares `(row, column)` inside the board (so at most one tree
per square). Two squares are adjacent, orthogonally or diagonally, when they differ by at most
one in each coordinate (`Battleships.Near`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the board row by row, each entry the park of its square. -/
abbrev ParksPuzzleInstance := List (List ℕ)

/-- The number of rows `m` (also the number of parks). -/
def rows (i : ParksPuzzleInstance) : ℕ := i.length

/-- The number of columns `n` (the length of the first row). -/
def cols (i : ParksPuzzleInstance) : ℕ := (i.headD []).length

/-- The park of square `x = (row, column)`. -/
def park (i : ParksPuzzleInstance) (x : ℕ × ℕ) : ℕ :=
  (i.getD x.1 []).getD x.2 0

/-- Well-formedness: at least one row and one column, rows of equal length, park indices below
the number of rows `m`, and each of the `m` parks contains a square. -/
def WellFormed (i : ParksPuzzleInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    (∀ row ∈ i, ∀ k ∈ row, k < rows i) ∧
    ∀ k < rows i, ∃ x : ℕ × ℕ, x.1 < rows i ∧ x.2 < cols i ∧ park i x = k

/-- The set of squares `T` is a placement of trees solving the `(c, r)`-tree puzzle. -/
def Solves (c r : ℕ) (i : ParksPuzzleInstance) (T : Finset (ℕ × ℕ)) : Prop :=
  -- trees are placed on squares of the board, at most one per square
  (∀ x ∈ T, x.1 < rows i ∧ x.2 < cols i) ∧
  -- each column contains exactly `c` trees
  (∀ j < cols i, (T.filter fun x => x.2 = j).card = c) ∧
  -- each row contains exactly `r` trees
  (∀ k < rows i, (T.filter fun x => x.1 = k).card = r) ∧
  -- each park contains exactly `r` trees
  (∀ k < rows i, (T.filter fun x => park i x = k).card = r) ∧
  -- no two trees are on adjacent squares, not even diagonally
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ Battleships.Near x y

/-- Some placement of trees solves the `(c, r)`-tree puzzle. -/
def ParksPuzzleFeasible (c r : ℕ) (i : ParksPuzzleInstance) : Prop :=
  ∃ T : Finset (ℕ × ℕ), Solves c r i T

open Classical in
/-- `(c, r)`-TREE PARKS PUZZLE as a decision problem over bitstrings. -/
noncomputable def parksPuzzleDec (c r : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ParksPuzzleInstance) x with
  | some i => decide (WellFormed i ∧ ParksPuzzleFeasible c r i)
  | none => false

/-- **`(c, r)`-TREE PARKS PUZZLE is NP-complete for all positive integers `c` and `r`.**
Source: Minevich, Cunningham, Karan and Gyllinsky (2024), Theorem 2. -/
public theorem_wanted parksPuzzle_npComplete (c r : ℕ) (_hc : 1 ≤ c) (_hr : 1 ≤ r) :
    parksPuzzleDec c r ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (parksPuzzleDec c r)

end MetaMathlibExt.Complexity.NPComplete.ParksPuzzle
