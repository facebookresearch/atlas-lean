/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DETOUR is NP-complete

Source:
H. Tang, "On the NP-completeness of satisfying certain path and loop puzzles",
arXiv:2004.12849 (2020), Sections 1.4, 2 and 3.5.
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

namespace MetaMathlibExt.Complexity.NPComplete.Detour

/-!
# DETOUR is NP-complete

INSTANCE: a rectangular grid divided into regions, some regions carrying a number.
QUESTION: is there an orthogonal loop passing through each cell exactly once such that, in every
region with a number, the loop turns exactly that many times?

Tang (Section 1.4): "In Detour, the player is given a rectangular grid divided into regions. The
aim is to draw an orthogonal loop passing through each cell exactly once. Some regions may
contain a small number: this number indicates the number of times the loop turns within this
region." Section 2 shows membership in NP and Section 3.5 NP-hardness, so deciding solvability
is NP-complete.

The cells of an `h × w` grid are `Fin h × Fin w`, adjacent when orthogonally neighboring (the
box product of two path graphs, as in `WantedExt.Complexity.NPComplete.PathPuzzleWanted`). A loop
through each cell exactly once is a Hamiltonian cycle of this grid graph (Mathlib's
`Walk.IsHamiltonianCycle`). The loop turns at a cell when its two loop edges there are one
horizontal and one vertical, i.e. the two loop neighbors of the cell differ in both coordinates
(`IsTurn`). The regions are given by a label for each cell, and a clue `(r, k)` asks for exactly
`k` turns at the cells labeled `r`. Labels may name disconnected sets of cells; this class
contains the puzzles with connected regions, so it is NP-complete under either reading.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **DETOUR is NP-complete.** Source: Tang (2020), Sections 2 and 3.5. -/
public theorem_wanted detour_npComplete :
    detourDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L detourDec

end MetaMathlibExt.Complexity.NPComplete.Detour
