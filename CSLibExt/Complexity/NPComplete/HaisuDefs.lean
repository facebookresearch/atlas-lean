/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAISU: definitions

Source:
H. Tang, "On the NP-completeness of satisfying certain path and loop puzzles",
arXiv:2004.12849 (2020), Sections 1.2, 2 and 3;
puzzle rules: TheGreatEscaper, "HAISU (Room Count): An original grid-logic challenge",
Puzzling Stack Exchange, https://puzzling.stackexchange.com/q/48029/.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

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
