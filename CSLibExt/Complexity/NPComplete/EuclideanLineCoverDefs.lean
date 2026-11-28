/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanDefs

/-!
# EUCLIDEAN LINE COVER (covering lines by points): definitions

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
as in `CoveringPointsByLinesDefs`). The lines form a set, so the listed lines are distinct as
point sets of `ℝ × ℝ`. The `K` points are real points indexed by `Fin K` (repetitions allowed, so
"`K` points" and "at most `K` points" agree).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3 (1982),
381-395, doi:10.1016/0196-6774(82)90032-3 (comment on problem [2], the dual EUCLIDEAN LINE
COVER);
N. Megiddo and A. Tamir, "On the complexity of locating linear facilities in the plane",
Operations Research Letters 1 (1982), 194-197, doi:10.1016/0167-6377(82)90039-6.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EuclideanLineCover

open GeometricTravelingSalesman (toInt)

/-- A line `a x + b y = c`, given by its integer coefficients `(a, b, c)` in positive/negative-part
form. -/
abbrev Line := (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)

/-- An instance: the lines and the number of points `K`. -/
abbrev EuclideanLineCoverInstance := List Line × ℕ

/-- The point set `{(x, y) ∈ ℝ² | a x + b y = c}` of a line. -/
def lineSet (ℓ : Line) : Set (ℝ × ℝ) :=
  {p | (toInt ℓ.1 : ℝ) * p.1 + (toInt ℓ.2.1 : ℝ) * p.2 = (toInt ℓ.2.2 : ℝ)}

/-- Well-formedness of an instance: every line has `(a, b) ≠ (0, 0)`, the lines are distinct
as point sets, and `K` is positive. -/
def WellFormed (i : EuclideanLineCoverInstance) : Prop :=
  (∀ ℓ ∈ i.1, toInt ℓ.1 ≠ 0 ∨ toInt ℓ.2.1 ≠ 0) ∧ (i.1.map lineSet).Nodup ∧ 0 < i.2

/-- There are `K` points of `ℝ × ℝ` such that every line contains one of them. -/
def EuclideanLineCoverFeasible (i : EuclideanLineCoverInstance) : Prop :=
  ∃ q : Fin i.2 → ℝ × ℝ, ∀ ℓ ∈ i.1, ∃ j, q j ∈ lineSet ℓ

open Classical in
/-- EUCLIDEAN LINE COVER as a decision problem over bitstrings. -/
noncomputable def euclideanLineCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EuclideanLineCoverInstance) x with
  | some i => decide (WellFormed i ∧ EuclideanLineCoverFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EuclideanLineCover
