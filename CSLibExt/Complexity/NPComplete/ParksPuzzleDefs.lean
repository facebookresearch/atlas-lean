/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# (c, r)-TREE PARKS PUZZLE: definitions

Source:
I. Minevich, G. Cunningham, K. A. Karan and J. V. Gyllinsky, "Parks: A Doubly Infinite Family
of NP-Complete Puzzles and Generalizations of A002464", arXiv:2411.02251 (2024), Definition 1,
Section IV and Theorem 2.
-/
module

public import Mathlib.Data.Finset.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BattleshipsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ParksPuzzle

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

end MetaMathlibExt.Complexity.NPComplete.ParksPuzzle
