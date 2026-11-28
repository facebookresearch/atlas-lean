/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED FREECELL is NP-complete

Source:
M. Helmert, "Complexity results for standard benchmark domains in planning", Artificial
Intelligence 143(2) (2003), 219-262, doi:10.1016/S0004-3702(02)00364-8, Section 4.3,
Definitions 44 (FREECELL task) and 45 (FREECELL domain) and Theorem 46 (plan existence for
FREECELL is NP-complete, even for an arbitrary fixed number of free cells).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FreeCellDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FreeCell

/-!
# GENERALIZED FREECELL is NP-complete

INSTANCE (a FREECELL task `(n, w, c, T)`, Helmert, Definition 44): a suit length `n`, a tableau
width `w`, a free cell count `c`, and an initial tableau `T`: at most `w` non-empty sequences
(tableau piles) of cards of the `n`-deck `{♦, ♥, ♣, ♠} × {1, …, n}` in which every card of the
deck appears exactly once.
QUESTION: can all cards be moved to the foundations by legal moves (plan existence for the
FREECELL domain, Definition 45)?

Moves (Definition 45). A state is a pair `(T, F)` of a tableau and the set `F` of free cell
cards, `|F| ≤ c`; cards in neither are on the foundations. The initial state is `(T, ∅)`, the
goal is `(∅, ∅)`. The last card of a pile is its top card. A move is a pickup followed by a drop
of the same card. Pickups: from a free cell; from the tableau, when the card is the only card of
its pile (the pile disappears); from a tableau pile, when the card is the top card of a pile with
a non-empty buried part. Drops: in a free cell, when fewer than `c` free cells are occupied; on
the tableau, as a new one-card pile, when there are fewer than `w` piles; on a tableau pile whose
top card it matches (different colour, value one less); at the foundations, when no tableau or
free cell card of the same suit has a lower value.

Cards are pairs `(suit, value)` with suits `0, 1, 2, 3` standing for `♦, ♥, ♣, ♠`, so a card is
red iff its suit is below `2`. Piles are lists listed from the bottom card to the top card;
the tableau and the free cells are lists whose order is immaterial (every move may act at any
position).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GENERALIZED FREECELL is NP-complete.** Source: Helmert (2003), Theorem 46. -/
public theorem_wanted freeCell_npComplete :
    freeCellDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L freeCellDec

end MetaMathlibExt.Complexity.NPComplete.FreeCell
