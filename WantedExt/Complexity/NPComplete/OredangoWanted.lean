/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OREDANGO is NP-complete

Source:
T. Takahata, N. Minamikawa and T. Okuno, "Computational complexity and integer programming
formulation of the Oredango puzzle", arXiv:2503.10393 (2025) (Section 1, rules (a)-(d) and
Theorem 1.1).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.OredangoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Oredango

/-!
# OREDANGO is NP-complete

INSTANCE: an `m × n` grid (`m, n ≥ 1`) with white circles in some cells, joined by skewers, and
nonnegative integers in some circles. Each skewer is a chain of circles in which consecutive
circles are in side-adjacent cells; a circle joined to no other circle forms a skewer of length
zero, so every circle is on exactly one skewer; each circle holds at most one integer and each
skewer at most one circle with an integer. QUESTION: can some circles be colored black so that
(a) in any skewer, the number of black circles equals the integer inside its circles;
(b) in any skewer, no three consecutive circles have the same color (white or black);
(c) in any row of the grid, no three consecutive circles have the same color;
(d) in any column of the grid, no three consecutive circles have the same color?
In rows and columns, cells without circles are skipped.

This is the Oredango Decision Problem of Takahata, Minamikawa and Okuno, who prove Oredango
ASP-complete (Theorem 1.1): the problem of finding another solution beyond `k` given ones is
NP-complete for every `k ≥ 0`, and `k = 0` is this decision problem. Membership in NP: the
coloring is a certificate.

The cells are pairs `(row, column)` with `row < m` and `column < n`. Each skewer is listed as its
circles in order along the skewer, together with its integer, if any, as a flag and a value (the
rules read the integer of a skewer, not the circle that holds it). The circles are all listed
cells. A coloring is a map `black` from cells to `Bool`. Three circles are consecutive in a row
when they lie in that row in increasing columns with no circle of the row strictly between
the first and second or between the second and third; columns likewise.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **OREDANGO is NP-complete.** Source: Takahata, Minamikawa and Okuno (2025), Theorem 1.1. -/
public theorem_wanted oredango_npComplete :
    oredangoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L oredangoDec

end MetaMathlibExt.Complexity.NPComplete.Oredango
