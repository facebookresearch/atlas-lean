/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EUCLIDEAN LINE COVER (covering lines by points) is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3 (1982),
381-395, doi:10.1016/0196-6774(82)90032-3 (comment on problem [2], the dual EUCLIDEAN LINE
COVER);
N. Megiddo and A. Tamir, "On the complexity of locating linear facilities in the plane",
Operations Research Letters 1 (1982), 194-197, doi:10.1016/0167-6377(82)90039-6.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EuclideanLineCoverDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EuclideanLineCover

open GeometricTravelingSalesman (toInt)

/-!
# EUCLIDEAN LINE COVER (covering lines by points) is NP-complete

INSTANCE: a finite set of straight lines in the plane, each given by integer coefficients, and a
positive integer `K`. QUESTION: are there `K` points such that each line contains one of the
points?

Johnson (1982), after problem [2] (covering points by lines,
`CoveringPointsByLinesWanted`): "The dual EUCLIDEAN LINE COVER problem, in which we are given a
set of (infinite) straight lines and are asked if there exist `K` points such that each line
contains one of the points, is also NP-complete, but solvable in polynomial time if there are no
intersections involving three or more lines", citing Megiddo and Tamir. Megiddo and Tamir
(1982), abstract: it is NP-hard in the strong sense to locate `r` lines minimizing any isotone
function of the distances from given points to their nearest lines, and "the results also apply
to the situation where the demand is represented by `r` lines and the facilities by `n` single
points"; all distances `0` is this problem. Membership in NP: a point on several input lines can
be taken at an intersection of two of them and a point on a single line at a point of that line
with rational coordinates of polynomial size, so the points are a certificate.

A line `a x + b y = c` is given by its integer coefficients `(a, b, c)` with `(a, b) ≠ (0, 0)`,
each integer a pair `(p, q)` of naturals standing for `p - q` (`GeometricTravelingSalesman.toInt`,
as in `CoveringPointsByLinesWanted`). The lines form a set, so the listed lines are distinct as
point sets of `ℝ × ℝ`. The `K` points are real points indexed by `Fin K` (repetitions allowed, so
"`K` points" and "at most `K` points" agree).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EUCLIDEAN LINE COVER is NP-complete.** Source: Megiddo and Tamir (1982); Johnson (1982). -/
public theorem_wanted euclideanLineCover_npComplete :
    euclideanLineCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L euclideanLineCoverDec

end MetaMathlibExt.Complexity.NPComplete.EuclideanLineCover
