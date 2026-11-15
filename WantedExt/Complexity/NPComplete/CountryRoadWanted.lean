/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COUNTRY ROAD is NP-complete

Source:
A. Ishibashi, Y. Sato and S. Iwata, "NP-completeness of two pencil puzzles: Yajilin and Country
Road", Utilitas Mathematica 88 (2012), 237-246;
H. Tang, "A framework for loop and path puzzle satisfiability NP-hardness results",
arXiv:2202.02046 (2022), Section 3.7.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CountryRoad

/-!
# COUNTRY ROAD is NP-complete

Country Road (Nikoli) is played on a rectangular grid divided into regions, some of which carry
a number. Tang (2022, Section 3.7) states its rules: "Draw a single loop passing between
adjacent cell centres and visiting each region once. A number within a region indicates the
number of cells in that region through which the loop passes. Out of any pair of adjacent cells
in different regions, at least one must be used by the loop."

INSTANCE: a rectangular grid partitioned into regions, each a connected set of cells, some
regions carrying a number.
QUESTION: is there a loop satisfying these rules?

Ishibashi, Sato and Iwata (2012) prove this NP-complete; Tang (2022, Section 3.7) reproves
NP-hardness with a T-metacell gadget and notes that a solution is checked in polynomial time.

Representation. The grid is given explicitly, row by row: entry `c` of row `r` is the region of
cell `(r, c)`, and the regions are `0, …, R - 1`, where `R` is the length of the list of region
numbers; entry `k` of that list is `0` when region `k` has no number and `v + 1` when it carries
the number `v`. The grid is explicit, so its area is at most the encoded input length.
`WellFormed` requires at least one row and one column, rows of equal length, region indices
below `R`, and every region a nonempty connected set of cells (as in
`WantedExt.Complexity.NPComplete.MoonOrSunWanted`). Cells are `Fin m × Fin n`, adjacent when
they share a side in Mathlib's grid graph `pathGraph m □ pathGraph n`. The loop through cell
centres is a cycle `c` of this graph (`SimpleGraph.Walk.IsCycle`); its cells, the cells the loop
passes through or uses, are `c.support`. The loop visits each region once: it meets every
region, and enters each region (moves from a cell outside it to a cell inside it, a dart of `c`)
at most once, so its cells in each region form one contiguous stretch of the loop (the loop never
enters a region only when it lies inside that one region).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **COUNTRY ROAD is NP-complete.** Source: Ishibashi, Sato and Iwata (2012); Tang (2022),
Section 3.7. -/
public theorem_wanted countryRoad_npComplete :
    countryRoadDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L countryRoadDec

end MetaMathlibExt.Complexity.NPComplete.CountryRoad
