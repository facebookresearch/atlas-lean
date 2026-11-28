/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NAGENAWA: definitions

Source:
L. T. Bordin, A. de A. S. Braga, B. A. de Mello and S. da S. Feitosa, "Nagenawa is
NP-complete", Journal of Information Processing 34 (2026), 112-120,
doi:10.2197/ipsjjip.34.112.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Nagenawa

/-- An instance: the grid row by row (the region index of each cell), and for each region whether
it is numbered and its number. -/
abbrev NagenawaInstance := List (List ℕ) × List (Bool × ℕ)

/-- The number of rows. -/
abbrev rows (i : NagenawaInstance) : ℕ := i.1.length

/-- The number of columns, the length of the first row. -/
abbrev cols (i : NagenawaInstance) : ℕ := (i.1.headD []).length

/-- The cells of the grid. -/
abbrev Cell (i : NagenawaInstance) := Fin (rows i) × Fin (cols i)

/-- The region of the cell in row `p.1` and column `p.2`. -/
def region (i : NagenawaInstance) (p : Cell i) : ℕ := (i.1.getD p.1 []).getD p.2 0

/-- The grid graph: cells are adjacent when they share a side. -/
abbrev grid (h w : ℕ) : SimpleGraph (Fin h × Fin w) :=
  SimpleGraph.pathGraph h □ SimpleGraph.pathGraph w

/-- Well-formedness of an instance: at least one row and one column, rows of equal length,
region indices in range, every region connected, and `0` stored for unnumbered regions. -/
def WellFormed (i : NagenawaInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.1, row.length = cols i) ∧
    (∀ row ∈ i.1, ∀ k ∈ row, k < i.2.length) ∧
    (∀ k < i.2.length, ((grid (rows i) (cols i)).induce {p | region i p = k}).Connected) ∧
    ∀ e ∈ i.2, e.1 = false → e.2 = 0

/-- A rectangular loop `(r₁, c₁, r₂, c₂)`: the boundary of the rectangle with corner cells
`(r₁, c₁)` and `(r₂, c₂)`. -/
abbrev Loop := ℕ × ℕ × ℕ × ℕ

/-- The loop `L` lies in an `m × n` grid and is a rectangle: `r₁ < r₂ < m` and `c₁ < c₂ < n`. -/
def IsLoop (m n : ℕ) (L : Loop) : Prop :=
  L.1 < L.2.2.1 ∧ L.2.2.1 < m ∧ L.2.1 < L.2.2.2 ∧ L.2.2.2 < n

/-- The loop `L` crosses the cell `(r, c)`. -/
def Crosses (L : Loop) (r c : ℕ) : Prop :=
  ((r = L.1 ∨ r = L.2.2.1) ∧ L.2.1 ≤ c ∧ c ≤ L.2.2.2) ∨
    ((c = L.2.1 ∨ c = L.2.2.2) ∧ L.1 ≤ r ∧ r ≤ L.2.2.1)

/-- The cell `(r, c)` is a corner of the loop `L`. -/
def IsCorner (L : Loop) (r c : ℕ) : Prop :=
  (r = L.1 ∨ r = L.2.2.1) ∧ (c = L.2.1 ∨ c = L.2.2.2)

/-- The unit segment from the center of cell `(r, c)` to the center of cell `(r, c + 1)` is an
edge of the loop `L`. -/
def HasHorizontalEdge (L : Loop) (r c : ℕ) : Prop :=
  (r = L.1 ∨ r = L.2.2.1) ∧ L.2.1 ≤ c ∧ c + 1 ≤ L.2.2.2

/-- The unit segment from the center of cell `(r, c)` to the center of cell `(r + 1, c)` is an
edge of the loop `L`. -/
def HasVerticalEdge (L : Loop) (r c : ℕ) : Prop :=
  (c = L.2.1 ∨ c = L.2.2.2) ∧ L.1 ≤ r ∧ r + 1 ≤ L.2.2.1

/-- Two loops share no corner and no edge. -/
def Compatible (L L' : Loop) : Prop :=
  ∀ r c, ¬ (IsCorner L r c ∧ IsCorner L' r c) ∧
    ¬ (HasHorizontalEdge L r c ∧ HasHorizontalEdge L' r c) ∧
    ¬ (HasVerticalEdge L r c ∧ HasVerticalEdge L' r c)

/-- The list of loops `S` solves the instance: every member is a rectangular loop in the grid,
distinct members share no corner and no edge, and every numbered region has exactly its number
of cells crossed by some loop. -/
def Solves (i : NagenawaInstance) (S : List Loop) : Prop :=
  (∀ L ∈ S, IsLoop (rows i) (cols i) L) ∧ S.Pairwise Compatible ∧
    ∀ k < i.2.length, (i.2.getD k (false, 0)).1 = true →
      {p : Cell i | region i p = k ∧ ∃ L ∈ S, Crosses L p.1 p.2}.ncard =
        (i.2.getD k (false, 0)).2

/-- Some list of rectangular loops solves the instance. -/
def NagenawaFeasible (i : NagenawaInstance) : Prop :=
  ∃ S : List Loop, Solves i S

open Classical in
/-- NAGENAWA as a decision problem over bitstrings. -/
noncomputable def nagenawaDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NagenawaInstance) x with
  | some i => decide (WellFormed i ∧ NagenawaFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Nagenawa
