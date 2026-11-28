/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# YOSENABE is NP-complete

Source:
C. Iwamoto, "Yosenabe is NP-complete", Journal of Information Processing 22(1) (2014), 40-43,
doi:10.2197/ipsjjip.22.40.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.YosenabeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Yosenabe

/-!
# YOSENABE is NP-complete

INSTANCE: a rectangular grid in which some cells are gray, two gray cells being connected when
they are adjacent vertically or horizontally (a set of connected gray cells is a gray area); some
gray areas are labelled with numbers, and some non-gray cells contain circles with numbers.
QUESTION: can arrows be drawn vertically or horizontally from all circles to gray areas so that
(i) the arrows do not bend and do not cross other circles or lines of other arrows, (ii) the
number of a labelled gray area equals the total of the numbers of the circles that enter it, and
(iii) at least one circle (arrow tip) enters each gray area?

The grid is given explicitly, row by row: each cell is `(k, a)` with `k = 0` an empty white cell,
`k = 1` a white cell with a circle numbered `a`, and `k = 2` a gray cell, labelled `a` if `a ≠ 0`.
Gray areas are the connected components of the gray cells in the grid graph
`pathGraph m □ pathGraph n` (`SameArea`). A solution gives every circle `x` the tip `tip x` of
its arrow, a gray cell in the same row or column; the arrow's line is the cells from `x`
(excluded) to `tip x` (included) (`OnArrow`), and the circle enters the gray area of its tip. As
in the source's rule (i), the only restrictions on a line are that it does not bend, contains no
circle, and shares no cell with the line of another arrow; in particular at most one arrow tip
enters each gray cell, as the source notes. The source does not forbid a line from passing over
gray cells before its tip, so neither does the statement.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **YOSENABE is NP-complete.** Source: Iwamoto (2014). -/
public theorem_wanted yosenabe_npComplete :
    yosenabeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L yosenabeDec

end MetaMathlibExt.Complexity.NPComplete.Yosenabe
