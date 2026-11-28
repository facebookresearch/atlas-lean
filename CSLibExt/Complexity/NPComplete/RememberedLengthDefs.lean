/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REMEMBERED LENGTH: definitions

Source:
P. Eua-anant, P. Apinyanon, T. Jirachaisri, N. Ruangsuksriwong and S. Ruangwises,
"NP-Completeness Proofs of All or Nothing, Water Walk, and Remembered Length Using the
T-Metacell Framework", arXiv:2510.21938 (2025), Section 2.3;
puzzle rules: puzz.link, "Remembered Length", https://puzz.link/rules.html?remlen.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RememberedLength

/-- An instance: the region numbers (`0` = unnumbered), and the grid row by row, each cell
`(region, shaded)`. -/
abbrev RememberedLengthInstance := List ℕ × List (List (ℕ × Bool))

/-- The number of rows. -/
def rows (i : RememberedLengthInstance) : ℕ := i.2.length

/-- The number of columns (the length of the first row). -/
def cols (i : RememberedLengthInstance) : ℕ := (i.2.headD []).length

/-- The entry `(region, shaded)` of cell `x`. -/
def cell (i : RememberedLengthInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ × Bool :=
  (i.2.getD x.1 []).getD x.2 (0, false)

/-- The number of region `k` (`0` = unnumbered). -/
def number (i : RememberedLengthInstance) (k : ℕ) : ℕ := i.1.getD k 0

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : RememberedLengthInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: at least one row and one column, rows of equal length, region indices
below `R`, and every region a nonempty connected set of cells. -/
def WellFormed (i : RememberedLengthInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.2, row.length = cols i) ∧
    (∀ row ∈ i.2, ∀ e ∈ row, e.1 < i.1.length) ∧
    ∀ k < i.1.length, ((Grid i).induce {x | (cell i x).1 = k}).Connected

/-- The cycle `c` satisfies the rules: its cells are exactly the unshaded cells, and each time
it moves from a region numbered `k > 0` into another region, its next `k` cells, and not the
one after them, lie in that other region. -/
def Solves (i : RememberedLengthInstance) {u : Fin (rows i) × Fin (cols i)}
    (c : (Grid i).Walk u u) : Prop :=
  (∀ x, x ∈ c.support ↔ (cell i x).2 = false) ∧
  ∀ j < c.length, (cell i (c.getVert j)).1 ≠ (cell i (c.getVert (j + 1))).1 →
    0 < number i (cell i (c.getVert j)).1 →
      (∀ t, 1 ≤ t → t ≤ number i (cell i (c.getVert j)).1 →
        (cell i (c.getVert ((j + t) % c.length))).1 = (cell i (c.getVert (j + 1))).1) ∧
      (cell i (c.getVert ((j + number i (cell i (c.getVert j)).1 + 1) % c.length))).1 ≠
        (cell i (c.getVert (j + 1))).1

/-- Some cycle of the grid graph satisfies the rules. -/
def RememberedLengthFeasible (i : RememberedLengthInstance) : Prop :=
  ∃ u, ∃ c : (Grid i).Walk u u, c.IsCycle ∧ Solves i c

open Classical in
/-- REMEMBERED LENGTH as a decision problem over bitstrings. -/
noncomputable def rememberedLengthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RememberedLengthInstance) x with
  | some i => decide (WellFormed i ∧ RememberedLengthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RememberedLength
