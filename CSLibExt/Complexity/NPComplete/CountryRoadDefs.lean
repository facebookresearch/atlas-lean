/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COUNTRY ROAD: definitions

Source:
A. Ishibashi, Y. Sato and S. Iwata, "NP-completeness of two pencil puzzles: Yajilin and Country
Road", Utilitas Mathematica 88 (2012), 237-246;
H. Tang, "A framework for loop and path puzzle satisfiability NP-hardness results",
arXiv:2202.02046 (2022), Section 3.7.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CountryRoad

/-- An instance: the grid row by row, each entry the region of the cell, and the region numbers;
entry `k` is `0` when region `k` has no number and `v + 1` when it carries the number `v`. -/
abbrev CountryRoadInstance := List (List ℕ) × List ℕ

/-- The number of rows `m`. -/
abbrev rows (i : CountryRoadInstance) : ℕ := i.1.length

/-- The number of columns `n` (the length of the first row). -/
abbrev cols (i : CountryRoadInstance) : ℕ := (i.1.headD []).length

/-- The number of regions `R`. -/
abbrev regionCount (i : CountryRoadInstance) : ℕ := i.2.length

/-- A cell `(row, column)` of the grid. -/
abbrev Cell (i : CountryRoadInstance) := Fin (rows i) × Fin (cols i)

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : CountryRoadInstance) : SimpleGraph (Cell i) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- The region of cell `x`. -/
def region (i : CountryRoadInstance) (x : Cell i) : ℕ :=
  (i.1.getD x.1 []).getD x.2 0

/-- The number entry of region `k`: `0` for no number, `v + 1` for the number `v`. -/
def clue (i : CountryRoadInstance) (k : ℕ) : ℕ :=
  i.2.getD k 0

/-- Well-formedness: at least one row and one column, rows of equal length, region indices
below `R`, and every region a nonempty connected set of cells. -/
def WellFormed (i : CountryRoadInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.1, row.length = cols i) ∧
    (∀ row ∈ i.1, ∀ k ∈ row, k < regionCount i) ∧
    ∀ k < regionCount i, ((Grid i).induce {x | region i x = k}).Connected

/-- The cycle `c` satisfies the rules of Country Road. -/
def Solves (i : CountryRoadInstance) {u : Cell i} (c : (Grid i).Walk u u) : Prop :=
  -- the loop visits each region once: it meets every region, and enters each at most once
  (∀ k < regionCount i, ∃ x ∈ c.support, region i x = k) ∧
  (∀ k < regionCount i, (c.darts.filter fun d =>
      region i d.snd = k ∧ region i d.fst ≠ k).length ≤ 1) ∧
  -- a number is the number of cells of its region through which the loop passes
  (∀ k < regionCount i, clue i k ≠ 0 →
    (Finset.univ.filter fun x => region i x = k ∧ x ∈ c.support).card + 1 = clue i k) ∧
  -- of two adjacent cells in different regions, at least one is used by the loop
  ∀ x y, (Grid i).Adj x y → region i x ≠ region i y → x ∈ c.support ∨ y ∈ c.support

/-- Some cycle of the grid graph satisfies the rules. -/
def CountryRoadFeasible (i : CountryRoadInstance) : Prop :=
  ∃ u, ∃ c : (Grid i).Walk u u, c.IsCycle ∧ Solves i c

open Classical in
/-- COUNTRY ROAD as a decision problem over bitstrings. -/
noncomputable def countryRoadDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := CountryRoadInstance) x with
  | some i => decide (WellFormed i ∧ CountryRoadFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CountryRoad
