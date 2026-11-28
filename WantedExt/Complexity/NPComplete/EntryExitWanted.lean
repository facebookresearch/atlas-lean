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
public import CSLibExt.Complexity.NPComplete.EntryExitDefs

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

/-- **ENTRY EXIT is NP-complete.** Source: Kiatchaipipat and Ruangwises (2025), Section 2.2. -/
public theorem_wanted entryExit_npComplete :
    entryExitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L entryExitDec

end MetaMathlibExt.Complexity.NPComplete.EntryExit
