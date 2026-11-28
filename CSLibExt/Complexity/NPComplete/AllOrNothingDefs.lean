/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ALL OR NOTHING: definitions

Source:
P. Eua-anant, P. Apinyanon, T. Jirachaisri, N. Ruangsuksriwong and S. Ruangwises,
"NP-Completeness Proofs of All or Nothing, Water Walk, and Remembered Length Using the
T-Metacell Framework", arXiv:2510.21938 (2025), Section 2.1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AllOrNothing

/-- An instance: the number of regions `R`, and the grid row by row, each entry the region of
its cell. -/
abbrev AllOrNothingInstance := ℕ × List (List ℕ)

/-- The number of rows. -/
def rows (i : AllOrNothingInstance) : ℕ := i.2.length

/-- The number of columns (the length of the first row). -/
def cols (i : AllOrNothingInstance) : ℕ := (i.2.headD []).length

/-- The region of cell `x`. -/
def region (i : AllOrNothingInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ :=
  (i.2.getD x.1 []).getD x.2 0

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : AllOrNothingInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: at least one row and one column, rows of equal length, region indices
below `R`, and every region a nonempty connected set of cells. -/
def WellFormed (i : AllOrNothingInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.2, row.length = cols i) ∧
    (∀ row ∈ i.2, ∀ k ∈ row, k < i.1) ∧
    ∀ k < i.1, ((Grid i).induce {x | region i x = k}).Connected

/-- The cycle `c` satisfies rules 1-3. -/
def Solves (i : AllOrNothingInstance) {u : Fin (rows i) × Fin (cols i)} (c : (Grid i).Walk u u) :
    Prop :=
  -- 1. a visited region is visited in all of its cells
  (∀ x y, region i x = region i y → x ∈ c.support → y ∈ c.support) ∧
  -- 2. the loop enters each region at most once
  (∀ k < i.1, (c.darts.filter fun d =>
      region i d.snd = k ∧ region i d.fst ≠ k).length ≤ 1) ∧
  -- 3. no two unvisited regions are adjacent
  ∀ x y, (Grid i).Adj x y → region i x ≠ region i y → x ∈ c.support ∨ y ∈ c.support

/-- Some cycle of the grid graph satisfies the rules. -/
def AllOrNothingFeasible (i : AllOrNothingInstance) : Prop :=
  ∃ u, ∃ c : (Grid i).Walk u u, c.IsCycle ∧ Solves i c

open Classical in
/-- ALL OR NOTHING as a decision problem over bitstrings. -/
noncomputable def allOrNothingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AllOrNothingInstance) x with
  | some i => decide (WellFormed i ∧ AllOrNothingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.AllOrNothing
