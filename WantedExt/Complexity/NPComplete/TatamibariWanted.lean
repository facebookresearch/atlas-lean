/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TATAMIBARI is NP-complete

Source:
A. Adler, J. Bosboom, E. D. Demaine, M. L. Demaine, Q. C. Liu and J. Lynch, "Tatamibari is
NP-complete", 10th International Conference on Fun with Algorithms (FUN 2021), LIPIcs 157
(2020), 1:1-1:24, doi:10.4230/LIPIcs.FUN.2021.1 (arXiv:2003.08331).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TatamibariDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Tatamibari

/-!
# TATAMIBARI is NP-complete

INSTANCE: a rectangular `m × n` grid of unit-square cells, some `k` of which contain one of
three kinds of clues: `+` ("square"), `-` ("horizontal") and `|` ("vertical").
QUESTION: is there a set of `k` grid-aligned rectangles such that
1. the rectangles are disjoint;
2. the rectangles together cover all cells of the puzzle;
3. each rectangle contains exactly one clue;
4. the rectangle containing a `+` clue is a square (equal width and height);
5. the rectangle containing a `-` clue has greater width than height;
6. the rectangle containing a `|` clue has greater height than width; and
7. no four rectangles share the same corner?

Cells are `(r, c)` with row `r < m` and column `c < n`. The clues are listed; the rectangle of
a solution that contains clue `j` is called rectangle `j`. Since there are `k` rectangles, each
containing exactly one of the `k` clues, and the rectangles are disjoint, this numbering is a
bijection between the rectangles and the clues. Corners are points of the integer lattice:
the rectangle with top-left cell `(r, c)`, height `h` and width `w` has corners `(r, c)`,
`(r + h, c)`, `(r, c + w)` and `(r + h, c + w)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TATAMIBARI is NP-complete.** Source: Adler, Bosboom, Demaine, Demaine, Liu and Lynch
(2020). -/
public theorem_wanted tatamibari_npComplete :
    tatamibariDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L tatamibariDec

end MetaMathlibExt.Complexity.NPComplete.Tatamibari
