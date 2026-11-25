/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NAGENAWA is NP-complete

Source:
L. T. Bordin, A. de A. S. Braga, B. A. de Mello and S. da S. Feitosa, "Nagenawa is
NP-complete", Journal of Information Processing 34 (2026), 112-120,
doi:10.2197/ipsjjip.34.112.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Nagenawa

/-!
# NAGENAWA is NP-complete

A Nagenawa board is a rectangular grid of cells separated into outlined regions, which may or
may not be numbered. The cells are filled with any number of rectangular loops, using horizontal
or vertical segments that go across the centers of the cells, so that:
1. a number in an outlined region is the exact amount of its cells that are crossed by
   rectangular loops;
2. rectangular loops may cross each other, but cannot share a corner or an edge;
3. every segment is part of a loop, and there are no loose ends.

INSTANCE: a rectangular grid separated into regions, some of them numbered.
QUESTION: can rectangular loops be drawn so that rules 1-3 hold?

A rectangular loop is `(r₁, c₁, r₂, c₂)` with `r₁ < r₂` and `c₁ < c₂` inside the grid: the
boundary of the rectangle whose corner cells are `(r₁, c₁)`, `(r₁, c₂)`, `(r₂, c₁)`, `(r₂, c₂)`
(rows `0, …, m - 1` top to bottom, columns `0, …, n - 1`). It crosses the cells of rows `r₁`
and `r₂` between columns `c₁` and `c₂` and the cells of columns `c₁` and `c₂` between rows
`r₁` and `r₂`; it turns at its four corner cells, and its edges are the unit segments joining
the centers of consecutive crossed cells. Rule 2 says that two distinct loops of a solution
have no common corner cell and no common unit segment, so a cell crossed by both is a crossing
of a horizontal and a vertical side. Rule 3 holds because a solution is a list of rectangular
loops. A region is outlined: its cells are connected through cells of the region sharing a side,
as in Mathlib's grid graph `pathGraph m □ pathGraph n` on `Fin m × Fin n`.

The instance lists the rows of the grid, top to bottom, where entry `c` of a row is the index of
the region containing that cell, and gives for each region `k` the pair `(numbered, number)`,
entry `k` of the second component. `WellFormed` requires at least one row and one column, rows
of equal length, region indices in range, every region connected (in particular nonempty), and
the number `0` stored for every unnumbered region (no ignored payload).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **NAGENAWA is NP-complete.** Source: Bordin, Braga, de Mello and Feitosa (2026). -/
public theorem_wanted nagenawa_npComplete :
    nagenawaDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nagenawaDec

end MetaMathlibExt.Complexity.NPComplete.Nagenawa
