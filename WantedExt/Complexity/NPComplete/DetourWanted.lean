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
public import CSLibExt.Complexity.NPComplete.DetourDefs

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

/-- **DETOUR is NP-complete.** Source: Tang (2020), Sections 2 and 3.5. -/
public theorem_wanted detour_npComplete :
    detourDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L detourDec

end MetaMathlibExt.Complexity.NPComplete.Detour
