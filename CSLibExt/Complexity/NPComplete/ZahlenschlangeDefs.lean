/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ZAHLENSCHLANGE: definitions

Source:
N. Kiatchaipipat and S. Ruangwises, "NP-completeness proofs of puzzles using the T-metacell
framework", arXiv:2508.11570 (2025), Section 2.3.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Zahlenschlange

/-- An instance: the width `w` and the rows of numbers (`h` rows of `w` numbers). -/
abbrev ZahlenschlangeInstance := ℕ × List (List ℕ)

/-- A cell `(row, column)` of the grid. -/
abbrev Cell (i : ZahlenschlangeInstance) := Fin i.2.length × Fin i.1

/-- Orthogonal adjacency of cells: the grid graph, the box product of two path graphs. -/
abbrev gridGraph (i : ZahlenschlangeInstance) : SimpleGraph (Cell i) :=
  SimpleGraph.pathGraph i.2.length □ SimpleGraph.pathGraph i.1

/-- The number in a cell. -/
def number (i : ZahlenschlangeInstance) (u : Cell i) : ℕ :=
  (i.2.getD u.1 []).getD u.2 0

/-- Well-formedness of an instance: at least one row and one column, every row of `w`
numbers. -/
def WellFormed (i : ZahlenschlangeInstance) : Prop :=
  0 < i.1 ∧ 0 < i.2.length ∧ ∀ row ∈ i.2, row.length = i.1

/-- The puzzle has a solution: a path of the grid graph from the top left cell `s` to the bottom
right cell `t` on which, for the number of every cell `u`, exactly one cell holds that
number. -/
def ZahlenschlangeFeasible (i : ZahlenschlangeInstance) : Prop :=
  ∃ s t : Cell i, (s.1 : ℕ) = 0 ∧ (s.2 : ℕ) = 0 ∧ (t.1 : ℕ) + 1 = i.2.length ∧
    (t.2 : ℕ) + 1 = i.1 ∧ ∃ p : (gridGraph i).Walk s t, p.IsPath ∧
      ∀ u : Cell i, p.support.countP (fun v => number i v = number i u) = 1

open Classical in
/-- ZAHLENSCHLANGE as a decision problem over bitstrings. -/
noncomputable def zahlenschlangeDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x =>
    match MetaMathlibExt.BitstringEncoding.bitDecode (α := ZahlenschlangeInstance) x with
    | some i => decide (WellFormed i ∧ ZahlenschlangeFeasible i)
    | none => false

end MetaMathlibExt.Complexity.NPComplete.Zahlenschlange
