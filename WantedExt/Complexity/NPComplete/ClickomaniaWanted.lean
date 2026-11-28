/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLICKOMANIA (SAMEGAME) is NP-complete

Source:
T. C. Biedl, E. D. Demaine, M. L. Demaine, R. Fleischer, L. Jacobsen and J. I. Munro, "The
complexity of Clickomania", in R. J. Nowakowski (ed.), *More Games of No Chance*, MSRI
Publications 42, Cambridge University Press (2002), 389-404, doi:10.1017/9781316135167.029,
arXiv:cs/0107031.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ClickomaniaDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Clickomania

/-!
# CLICKOMANIA (SAMEGAME) is NP-complete

INSTANCE: a rectangular board initially full of square blocks, each colored one of finitely many
colors. QUESTION: is the puzzle solvable, i.e., can all blocks be removed by moves, where a move
selects (clicks) any group of size at least two (a group is a maximal connected monochromatic
polyomino), the blocks of the group disappear, any blocks stacked above them fall straight down as
far as they can, and every column that becomes empty of blocks is removed, bringing its two sides
closer to each other?

These are the rules of Biedl et al., Section 1. A board is the list of its columns from left to
right, each the list of the colors of its blocks from the bottom up; after settling no column has a
hole and after column shifting no column is empty, so this list describes every position reached.
Block `(c, r)` is the `r`-th block from the bottom of the `c`-th column; two blocks share an edge
when they are consecutive in one column, or in the same row of consecutive columns. The group of a
block is the set of blocks reached from it through edge-adjacent blocks of its color. Colors are
natural numbers; the number of colors is the number of distinct colors on the board.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CLICKOMANIA (SAMEGAME) is NP-complete.** Source: Biedl, Demaine, Demaine, Fleischer,
Jacobsen and Munro (2002). -/
public theorem_wanted clickomania_npComplete :
    clickomaniaDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L clickomaniaDec

end MetaMathlibExt.Complexity.NPComplete.Clickomania
