/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# YIN-YANG is NP-complete

Source:
E. D. Demaine, J. Lynch, M. Rudoy and Y. Uno, "Yin-Yang puzzles are NP-complete", Proceedings
of the 33rd Canadian Conference on Computational Geometry (CCCG 2021), arXiv:2106.15585.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.YinYangDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.YinYang

/-!
# YIN-YANG is NP-complete

INSTANCE: a rectangular grid whose cells each hold a black circle, a white circle, or nothing.
QUESTION: can every empty cell be given a black or a white circle so that the circles of each
color form a single orthogonally connected group and no `2 × 2` square holds four circles of the
same color?

Demaine, Lynch, Rudoy and Uno (Section 1): "a Yin-Yang puzzle consists of a rectangular `m × n`
grid of unit squares, called cells, where each cell either has a black circle, has a white
circle, or is empty. The goal of the puzzle is to fill each empty cell with either a black
circle or a white circle to satisfy the following two constraints: Connectivity constraint: For
each color (black and white), the circles of that color form a single connected group of cells,
where connectivity is according to four-way orthogonal adjacency. `2 × 2` constraint: No `2 × 2`
square contains four circles of the same color. In this paper, we prove NP-completeness of
deciding whether a Yin-Yang puzzle has a solution, with or without the `2 × 2` constraint." This
module states the puzzle with both constraints.

The cells of an `h × w` grid are `Fin h × Fin w`, adjacent when orthogonally neighboring (the
box product of two path graphs, as in `WantedExt.Complexity.NPComplete.EntryExitWanted`). A
filling is a color for every cell (`true` for black), agreeing with the given circles. "A single
connected group" of a color is `SimpleGraph.Connected` for the subgraph induced by the cells of
that color, which in particular has at least one cell.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **YIN-YANG is NP-complete.** Source: Demaine, Lynch, Rudoy and Uno (2021). -/
public theorem_wanted yinYang_npComplete :
    yinYangDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L yinYangDec

end MetaMathlibExt.Complexity.NPComplete.YinYang
