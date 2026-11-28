/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# HAISU: definitions

Tang (Section 1.2): "the player is given a rectangular grid divided into regions, including two
one-cell regions labelled with S for Start and F for Finish. The aim is to draw a directed
orthogonal path from S to F passing through every cell exactly once. Some numbers have been
given in the cells. A path may enter a region once or multiple times, if this is the `n`th time
the path enters the region, it may only pass over [blank] cells or instances of the number
`n`." (The printed "black cells" are the cells without a number; the puzzle's author states the
rule as "When your path passes over a cell with the big number `N`, it must be the `N`th time
you have entered the room.") Tang proves the puzzle NP-complete (Section 2, membership; Section
3, hardness).

INSTANCE: a rectangular grid of cells, each in a region and possibly carrying a positive number,
with a start cell `S` and a finish cell `F`, each the only cell of its region.
QUESTION: is there a path from `S` to `F` through orthogonally adjacent cells that passes
through every cell exactly once, such that whenever it passes over a cell with number `N`, the
current visit to that cell's region is the `N`th time the path has entered the region?

The grid is given row by row: entry `c` of row `r` is `(region, number, mark)` for cell
`(r, c)`, with number `0` for no number and mark `1` for `S`, `2` for `F`, `0` otherwise.
`WellFormed` requires at least one row and one column, rows of equal length, marks at most `2`,
exactly one cell marked `S` and one marked `F`, and each of them the only cell of its region.
Regions are arbitrary labels and need not be connected: this class contains the instances of
Tang's construction, so hardness transfers, and the membership argument does not use
connectivity.
Cells are `Fin m × Fin n`, adjacent in Mathlib's grid graph `pathGraph m □ pathGraph n`, and the
path is a Hamiltonian walk (`SimpleGraph.Walk.IsHamiltonian`) from `S` to `F`. Mathlib defines
`p.IsHamiltonian` as `∀ a, p.support.count a = 1`: every cell occurs exactly once in the walk, so
a walk that revisits a cell is excluded and the walk is a path
(`SimpleGraph.Walk.IsHamiltonian.isPath`). At step `t` the
path is at `c.getVert t`; the visits to a region `k` up to step `t` are the start (if `S` is in
`k`) and the moves among the first `t` that go from a cell outside `k` to a cell inside `k`. The
author's optional room-count clues (a small number giving the total number of entries into a
room) are not used in Tang's reduction and are not part of this statement.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
H. Tang, "On the NP-completeness of satisfying certain path and loop puzzles",
arXiv:2004.12849 (2020), Sections 1.2, 2 and 3;
puzzle rules: TheGreatEscaper, "HAISU (Room Count): An original grid-logic challenge",
Puzzling Stack Exchange, https://puzzling.stackexchange.com/q/48029/.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Haisu

/-- An instance: the grid row by row, each cell `(region, number, mark)`; number `0` means no
number, mark `1` is the start, mark `2` the finish. -/
abbrev HaisuInstance := List (List (ℕ × ℕ × ℕ))

/-- The number of rows. -/
def rows (i : HaisuInstance) : ℕ := i.length

/-- The number of columns (the length of the first row). -/
def cols (i : HaisuInstance) : ℕ := (i.headD []).length

/-- The entry `(region, number, mark)` of cell `x`. -/
def cell (i : HaisuInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ × ℕ × ℕ :=
  (i.getD x.1 []).getD x.2 (0, 0, 0)

/-- The region of cell `x`. -/
def region (i : HaisuInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ := (cell i x).1

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : HaisuInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: at least one row and one column, rows of equal length, marks at most `2`,
exactly one start cell and one finish cell, each the only cell of its region. -/
def WellFormed (i : HaisuInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    (∀ row ∈ i, ∀ e ∈ row, e.2.2 ≤ 2) ∧ ∀ mk ∈ ({1, 2} : Finset ℕ), ∃ x, (cell i x).2.2 = mk ∧
      (∀ y, (cell i y).2.2 = mk → y = x) ∧ ∀ y, region i y = region i x → y = x

/-- The path `c` from `s` meets the number clues: when it is at a cell `x` with number `N ≠ 0`
after `t` moves, `N` is the number of its visits so far to the region `k` of `x`, the start
counting as a visit when `s` lies in `k`. -/
def Solves (i : HaisuInstance) {s f : Fin (rows i) × Fin (cols i)} (c : (Grid i).Walk s f) :
    Prop :=
  ∀ t ≤ c.length, (cell i (c.getVert t)).2.1 ≠ 0 →
    (cell i (c.getVert t)).2.1 =
      (if region i s = region i (c.getVert t) then 1 else 0) +
        ((c.darts.take t).filter fun d =>
          region i d.snd = region i (c.getVert t) ∧
            region i d.fst ≠ region i (c.getVert t)).length

/-- Some path from the start cell to the finish cell through every cell exactly once meets the
number clues. -/
def HaisuFeasible (i : HaisuInstance) : Prop :=
  ∃ s f, (cell i s).2.2 = 1 ∧ (cell i f).2.2 = 2 ∧
    ∃ c : (Grid i).Walk s f, c.IsHamiltonian ∧ Solves i c

open Classical in
/-- HAISU as a decision problem over bitstrings. -/
noncomputable def haisuDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HaisuInstance) x with
  | some i => decide (WellFormed i ∧ HaisuFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Haisu
