/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# WATARIDORI: definitions

Ruangwises (2026), Section 1: "The puzzle consists of a rectangular grid partitioned into
polyominoes called regions. (A polyomino is a shape formed by one or more unit squares connected
orthogonally.) Some cells contain a circle, and some of these circles contain a number. The
objective of Wataridori is to connect all circles into pairs using paths that go between
horizontally or vertically adjacent cells. Paths cannot cross or share a cell with one another.
The two circles connected by a path must contain the same number, which must be equal to the
total number of regions the path passes through. A path may enter and exit a region at most
once. Circles without numbers are treated as wildcards and may represent any number. ... it is
not required for all cells in the grid to be covered by paths."

INSTANCE: a rectangular grid partitioned into regions, with circles in some cells, some of them
numbered.
QUESTION: can all circles be connected in pairs by paths satisfying these rules?

Representation. The instance lists the number `R` of regions and the grid row by row: entry `c`
of row `r` is `(region, mark)` for cell `(r, c)`, with mark `0` (no circle), `1` (circle without
a number) or `v + 2` (circle with number `v`). `WellFormed` requires at least one row and one
column, rows of equal length, region indices below `R`, and every region a nonempty connected set
of cells (a polyomino). Cells are `Fin m × Fin n`, adjacent when they share a side in Mathlib's
grid graph `pathGraph m □ pathGraph n`. A solution is a list of paths, each a walk between two
distinct circle cells that is a path (`SimpleGraph.Walk.IsPath`); no cell lies on two paths
(the supports, concatenated, have no duplicates); and every circle is an end of some path. A
circle then lies on exactly one path, as one of its ends. For each path, every numbered end
carries the number of distinct regions among the path's cells, so two numbered ends carry the
same number; and the path enters each region at most once, counting its start as an entry into
the start's region (so a path never returns to a region it has left).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
S. Ruangwises, "Wataridori is NP-complete", arXiv:2601.09345 (2026),
https://arxiv.org/abs/2601.09345.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Wataridori

/-- An instance: the number of regions `R`, and the grid row by row, each cell
`(region, mark)` with mark `0` (no circle), `1` (circle without number) or `v + 2` (circle with
number `v`). -/
abbrev WataridoriInstance := ℕ × List (List (ℕ × ℕ))

/-- The number of rows. -/
def rows (i : WataridoriInstance) : ℕ := i.2.length

/-- The number of columns (the length of the first row). -/
def cols (i : WataridoriInstance) : ℕ := (i.2.headD []).length

/-- The entry `(region, mark)` of cell `x`. -/
def cell (i : WataridoriInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ × ℕ :=
  (i.2.getD x.1 []).getD x.2 (0, 0)

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : WataridoriInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: at least one row and one column, rows of equal length, region indices
below `R`, and every region a nonempty connected set of cells. -/
def WellFormed (i : WataridoriInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.2, row.length = cols i) ∧
    (∀ row ∈ i.2, ∀ e ∈ row, e.1 < i.1) ∧
    ∀ k < i.1, ((Grid i).induce {x | (cell i x).1 = k}).Connected

/-- A drawn path: its two ends `u`, `v` and a walk from `u` to `v`. -/
abbrev DrawnPath (i : WataridoriInstance) :=
  (u : Fin (rows i) × Fin (cols i)) × (v : Fin (rows i) × Fin (cols i)) × (Grid i).Walk u v

/-- The distinct regions a walk passes through. -/
def regions (i : WataridoriInstance) {u v : Fin (rows i) × Fin (cols i)} (w : (Grid i).Walk u v) :
    List ℕ :=
  (w.support.map fun x => (cell i x).1).dedup

/-- A drawn path obeys the rules for one path: it is a path between two distinct circles, each
numbered end carries the number of regions the path passes through, and it enters each region
at most once (its start counting as an entry). -/
def PathOK (i : WataridoriInstance) (p : DrawnPath i) : Prop :=
  p.2.2.IsPath ∧ p.1 ≠ p.2.1 ∧ 1 ≤ (cell i p.1).2 ∧ 1 ≤ (cell i p.2.1).2 ∧
  (2 ≤ (cell i p.1).2 → (cell i p.1).2 = (regions i p.2.2).length + 2) ∧
  (2 ≤ (cell i p.2.1).2 → (cell i p.2.1).2 = (regions i p.2.2).length + 2) ∧
  ∀ k < i.1, (if (cell i p.1).1 = k then 1 else 0) +
    (p.2.2.darts.filter fun d => (cell i d.snd).1 = k ∧ (cell i d.fst).1 ≠ k).length ≤ 1

/-- Some list of paths obeys the rules, shares no cells, and pairs up all circles. -/
def WataridoriFeasible (i : WataridoriInstance) : Prop :=
  ∃ ps : List (DrawnPath i), (∀ p ∈ ps, PathOK i p) ∧
    (ps.flatMap fun p => p.2.2.support).Nodup ∧
    ∀ x, 1 ≤ (cell i x).2 → ∃ p ∈ ps, x = p.1 ∨ x = p.2.1

open Classical in
/-- WATARIDORI as a decision problem over bitstrings. -/
noncomputable def wataridoriDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WataridoriInstance) x with
  | some i => decide (WellFormed i ∧ WataridoriFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Wataridori
