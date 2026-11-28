/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SLITHER LINK is NP-complete

Source:
T. Yato, "On the NP-completeness of the Slither Link puzzle", IPSJ SIG Notes AL-74 (2000),
25-32;
T. Yato and T. Seta, "Complexity and completeness of finding another solution and its
application to puzzles", IEICE Transactions on Fundamentals of Electronics, Communications and
Computer Sciences E86-A(5) (2003), 1052-1060;
T. Yato, "Complexity and completeness of finding another solution and its application to
puzzles", Master's thesis, University of Tokyo (2003), Section 3.1, Theorem 3.3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SlitherLinkDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SlitherLink

/-!
# SLITHER LINK is NP-complete

Yato (2003, Section 3.1) states the rules of Slither Link:
* "Each problem is given as a rectangular lattice. The length of sides of the rectangle (as to
  the unit length of lattice) is called the size of the problem."
* "A 1 × 1 square surrounded by four points is called a cell. A cell may have a number out of
  0, 1, 2 or 3."
* "The goal is to make a loop which does not intersect or branch by connecting adjacent dots
  with lines, so that a number on the cell is equal to the number of lines drawn around it."

INSTANCE: an `m × n` rectangular lattice of cells (`m, n ≥ 1`), some cells carrying a number
in `{0, 1, 2, 3}`.
QUESTION: is there a loop along lattice lines, without crossings or branches, such that every
numbered cell has exactly that many of its four sides on the loop?

Yato (2000) proved this NP-complete. Yato and Seta (2003) and Yato (2003, Theorem 3.3) prove
that finding a solution is ASP-complete, and Yato (2003, Theorem 2.7, with `n = 0`) shows that
the decision problem of an ASP-complete problem is NP-complete.

Representation. The cells are given explicitly, row by row: entry `k` of row `r` is `0` when
cell `(r, k)` has no number and `v + 1` when it carries the number `v`, so the instance size is
proportional to the area of the lattice. `WellFormed` requires at least one row and one column,
rows of equal length and entries at most `4`. The lattice points of an `m × n` lattice are
`Fin (m + 1) × Fin (n + 1)` (row, column); adjacent dots, at distance one, are adjacent in
Mathlib's grid graph `pathGraph (m + 1) □ pathGraph (n + 1)`. Cell `(r, k)` is the square with
corners `(r, k)`, `(r, k + 1)`, `(r + 1, k)` and `(r + 1, k + 1)`, and its four sides are the
lattice edges between consecutive corners. A loop that does not intersect or branch is a cycle
`c` of the lattice graph (`SimpleGraph.Walk.IsCycle`), and the lines drawn are its edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SLITHER LINK is NP-complete.** Source: Yato (2000); Yato and Seta (2003); Yato (2003),
Theorem 3.3. -/
public theorem_wanted slitherLink_npComplete :
    slitherLinkDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L slitherLinkDec

end MetaMathlibExt.Complexity.NPComplete.SlitherLink
