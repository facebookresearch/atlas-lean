/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CORRAL (BAG) is NP-complete

Source:
E. Friedman, "Corral puzzles are NP-complete", manuscript, Stetson University (2002),
https://erich-friedman.github.io/papers/corral.pdf.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CorralDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Corral

/-!
# CORRAL (BAG) is NP-complete

Friedman (2002): "Each puzzle consists of a grid of squares, some of which contain numbers. The
goal is to find a closed loop containing some of the grid squares so that all the numbers are
inside the loop and each number is equal to the number of grid squares visible from it. A grid
square is visible from a number if it is horizontally or vertically aligned with it and all the
squares between them are inside the loop." The loop runs along the grid lines (Nikoli's Bag:
"a single, continuous loop along the lines of the grid"), and a visible square is itself inside
the loop, the numbered square included (Nikoli: the cells visible "before a line of the loop is
reached, plus the cell itself"). Friedman proves that deciding whether a Corral puzzle has a
solution is NP-complete, by a reduction from 3-coloring of planar graphs.

INSTANCE: an `m × n` grid of squares, some of which contain positive integers.
QUESTION: is there a closed loop along the grid lines such that every numbered square is inside
the loop and sees exactly its number of squares inside the loop (itself included) along its row
and column, without an outside square in between?

Representation. The grid is given row by row: entry `c` of row `r` is `0` for an empty square
and `k ≥ 1` for a square containing `k`, so the instance size is proportional to the area of
the grid plus the binary length of the numbers. The grid lines form Mathlib's grid graph
`pathGraph (m + 1) □ pathGraph (n + 1)` on the corner points `(r, c)`, `r ≤ m`, `c ≤ n`;
square `(r, c)` has corners `(r, c)`, `(r, c + 1)`, `(r + 1, c)` and `(r + 1, c + 1)`. A
closed loop along the grid lines is a cycle of this graph (`SimpleGraph.Walk.IsCycle`); it
does not cross or touch itself. A square is inside the loop when the horizontal ray from its
center to the right crosses the loop an odd number of times (the even-odd rule, which for a
simple closed polygon picks out its interior); the ray from the center of square `(r, c)`
crosses exactly the vertical unit segments `(r, d)`-`(r + 1, d)` with `c < d`. A square `y`
in the row or column of the numbered square `x` is visible from `x` when every square from `x`
to `y` (both included) is inside the loop.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CORRAL (BAG) is NP-complete.** Source: Friedman (2002). -/
public theorem_wanted corral_npComplete :
    corralDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L corralDec

end MetaMathlibExt.Complexity.NPComplete.Corral
