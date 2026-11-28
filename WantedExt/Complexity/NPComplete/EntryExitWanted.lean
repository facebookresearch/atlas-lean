/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ENTRY EXIT is NP-complete

Source:
N. Kiatchaipipat and S. Ruangwises, "NP-completeness proofs of puzzles using the T-metacell
framework", arXiv:2508.11570 (2025), Section 2.2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EntryExit

/-!
# ENTRY EXIT is NP-complete

INSTANCE: a rectangular grid divided into regions.
QUESTION: is there a single closed loop that traverses every cell exactly once while entering and
exiting each region exactly once?

Kiatchaipipat and Ruangwises (Section 2.2): "In Entry-Exit, the grid is divided into multiple
regions, and the goal is to find a single closed loop that traverses every cell exactly once
while entering and exiting each region exactly once"; they prove it ASP-complete by
parsimonious reductions, and a solution is checked in polynomial time, so deciding solvability
is NP-complete.

The cells of an `h × w` grid are `Fin h × Fin w`, adjacent when orthogonally neighboring (the
box product of two path graphs, as in `WantedExt.Complexity.NPComplete.PathPuzzleWanted`). A
closed loop traversing every cell exactly once is a Hamiltonian cycle of this grid graph
(Mathlib's `Walk.IsHamiltonianCycle`), traversed in one direction. The loop enters region `r`
along each of its steps (`Walk.darts`) from a cell outside `r` to a cell in `r`, and exits it
along each step from a cell in `r` to a cell outside; the rule is that each region is entered
exactly once and exited exactly once. The regions are given by a label for each cell. Labels may
name disconnected sets of cells; this class contains the puzzles with connected regions, so it
is NP-complete under either reading.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the width `w` and the rows of region labels; row lengths are checked by
`WellFormed`. -/
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

/-- **ENTRY EXIT is NP-complete.** Source: Kiatchaipipat and Ruangwises (2025), Section 2.2, an
unrefereed preprint. -/
public theorem_wanted entryExit_npComplete :
    entryExitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L entryExitDec

end MetaMathlibExt.Complexity.NPComplete.EntryExit
