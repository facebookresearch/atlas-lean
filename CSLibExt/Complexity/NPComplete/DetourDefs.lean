/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DETOUR: definitions

Source:
H. Tang, "On the NP-completeness of satisfying certain path and loop puzzles",
arXiv:2004.12849 (2020), Sections 1.4, 2 and 3.5.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Detour

/-- An instance: the width `w`, the rows of region labels (`h` rows of `w` labels), and the clues
`(r, k)`: the region labeled `r` has `k` turns. -/
abbrev DetourInstance := ℕ × List (List ℕ) × List (ℕ × ℕ)

/-- A cell `(row, column)` of the grid. -/
abbrev Cell (i : DetourInstance) := Fin i.2.1.length × Fin i.1

/-- Orthogonal adjacency of cells: the grid graph, the box product of two path graphs. -/
abbrev gridGraph (i : DetourInstance) : SimpleGraph (Cell i) :=
  SimpleGraph.pathGraph i.2.1.length □ SimpleGraph.pathGraph i.1

/-- The region label of a cell. -/
def region (i : DetourInstance) (u : Cell i) : ℕ :=
  (i.2.1.getD u.1 []).getD u.2 0

/-- The loop `W` turns at the cell `u`: two of its edges at `u` lead to cells differing from each
other in both coordinates, one horizontal and one vertical. -/
def IsTurn {i : DetourInstance} {v : Cell i} (W : (gridGraph i).Walk v v) (u : Cell i) : Prop :=
  ∃ a b : Cell i, s(u, a) ∈ W.edges ∧ s(u, b) ∈ W.edges ∧ a.1 ≠ b.1 ∧ a.2 ≠ b.2

/-- Well-formedness of an instance: every row has `w` labels. -/
def WellFormed (i : DetourInstance) : Prop :=
  ∀ row ∈ i.2.1, row.length = i.1

open Classical in
/-- The puzzle has a solution: a Hamiltonian cycle of the grid graph with exactly `k` turns at
the cells labeled `r`, for every clue `(r, k)`. -/
def DetourFeasible (i : DetourInstance) : Prop :=
  ∃ (v : Cell i) (W : (gridGraph i).Walk v v), W.IsHamiltonianCycle ∧
    ∀ q ∈ i.2.2, (Finset.univ.filter fun u => region i u = q.1 ∧ IsTurn W u).card = q.2

open Classical in
/-- DETOUR as a decision problem over bitstrings. -/
noncomputable def detourDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := DetourInstance) x with
  | some i => decide (WellFormed i ∧ DetourFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Detour
