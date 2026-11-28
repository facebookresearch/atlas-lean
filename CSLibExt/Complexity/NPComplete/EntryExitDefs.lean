/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ENTRY EXIT: definitions

Source:
N. Kiatchaipipat and S. Ruangwises, "NP-completeness proofs of puzzles using the T-metacell
framework", arXiv:2508.11570 (2025), Section 2.2.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EntryExit

/-- An instance: the width `w` and the rows of region labels (`h` rows of `w` labels). -/
abbrev EntryExitInstance := ℕ × List (List ℕ)

/-- A cell `(row, column)` of the grid. -/
abbrev Cell (i : EntryExitInstance) := Fin i.2.length × Fin i.1

/-- Orthogonal adjacency of cells: the grid graph, the box product of two path graphs. -/
abbrev gridGraph (i : EntryExitInstance) : SimpleGraph (Cell i) :=
  SimpleGraph.pathGraph i.2.length □ SimpleGraph.pathGraph i.1

/-- The region label of a cell. -/
def region (i : EntryExitInstance) (u : Cell i) : ℕ :=
  (i.2.getD u.1 []).getD u.2 0

/-- Well-formedness of an instance: every row has `w` labels. -/
def WellFormed (i : EntryExitInstance) : Prop :=
  ∀ row ∈ i.2, row.length = i.1

/-- The puzzle has a solution: a Hamiltonian cycle of the grid graph that, for the region `r` of
every cell, has exactly one step into `r` from outside and exactly one step out of `r`. -/
def EntryExitFeasible (i : EntryExitInstance) : Prop :=
  ∃ (v : Cell i) (W : (gridGraph i).Walk v v), W.IsHamiltonianCycle ∧
    ∀ u : Cell i,
      W.darts.countP (fun d => region i d.snd = region i u ∧ region i d.fst ≠ region i u) = 1 ∧
        W.darts.countP (fun d => region i d.fst = region i u ∧ region i d.snd ≠ region i u) = 1

open Classical in
/-- ENTRY EXIT as a decision problem over bitstrings. -/
noncomputable def entryExitDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := EntryExitInstance) x with
  | some i => decide (WellFormed i ∧ EntryExitFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EntryExit
