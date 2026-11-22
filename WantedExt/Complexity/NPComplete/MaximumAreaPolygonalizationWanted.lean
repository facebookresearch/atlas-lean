/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM AREA POLYGONALIZATION is NP-complete

Source:
S. P. Fekete, "On simple polygonalizations with optimal area", Discrete & Computational
Geometry 23 (2000), 73-110, doi:10.1007/PL00009492, Theorem 4.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinimumAreaPolygonalizationWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumAreaPolygonalization

open MetaMathlibExt.Complexity.NPComplete.QuadraticProgramming (ratVal)
open MetaMathlibExt.Complexity.NPComplete.MinimumAreaPolygonalization
  (MinimumAreaPolygonalizationInstance WellFormed point twiceSignedArea)

/-!
# MAXIMUM AREA POLYGONALIZATION is NP-complete

INSTANCE: a finite set `S` of points in the plane with integer coordinates, and a rational `A`.
QUESTION: is there a simple polygon with vertex set exactly `S` and area at least `A`?

This is the decision version of Fekete's MAX-AREA ("The related problem of maximizing the
enclosed area of a polygonalization is called MAX-AREA", Section 1, next to MIN-AREA: "Given a
finite set P of points in the Euclidean plane. Among all the simple polygons with vertex set P,
find one with minimal enclosed area") for points of the integer grid. Fekete's Theorem 4.1 shows
that GRID-FULL POLYGON is NP-hard: for grid points `P`, is there a simple polygon on the vertex
set `P` whose area attains the upper bound `n/2 + h_b(P)/2 + h_i(P) - 1` of his Theorem 2.2,
which no simple polygon on `P` exceeds? That is this question with `A` equal to the bound; the
abstract states NP-completeness of the area optimization problems.

The instance, its well-formedness, the polygon and its area are those of the merged sibling
`MinimumAreaPolygonalizationWanted`, reused unchanged: `MinimumAreaPolygonalizationInstance`
(the listed points with integer coordinates and `A` as a `QuadraticProgramming.RatCode`),
`MinimumAreaPolygonalization.WellFormed` (distinct points, positive denominator), a polygon with
vertex set exactly `S` as a permutation `σ` of the listed points, simple in the sense of the
shared `MathlibExt.Geometry.SegmentVisibilityShared.IsSimplePolygon`, and its enclosed area given
by the shoelace formula `|twiceSignedArea i σ| / 2`. Only the direction of the area bound
changes: at least `A` instead of at most `A`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some simple polygon with vertex set exactly `S` has area at least `A`: some cyclic order `σ`
of the points gives a simple polygon `p_{σ 0}, …, p_{σ (n-1)}` whose shoelace area is at least
`A`. -/
def MaximumAreaPolygonalizationFeasible (i : MinimumAreaPolygonalizationInstance) : Prop :=
  ∃ σ : Equiv.Perm (Fin i.1.length),
    MathlibExt.Geometry.SegmentVisibilityShared.IsSimplePolygon (point i ∘ σ) ∧
      ratVal i.2 ≤ (|twiceSignedArea i σ| : ℚ) / 2

open Classical in
/-- MAXIMUM AREA POLYGONALIZATION as a decision problem over bitstrings. -/
noncomputable def maximumAreaPolygonalizationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumAreaPolygonalizationInstance) x with
  | some i => decide (WellFormed i ∧ MaximumAreaPolygonalizationFeasible i)
  | none => false

/-- **MAXIMUM AREA POLYGONALIZATION is NP-complete.** Source: Fekete (2000), Theorem 4.1. -/
public theorem_wanted maximumAreaPolygonalization_npComplete :
    maximumAreaPolygonalizationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumAreaPolygonalizationDec

end MetaMathlibExt.Complexity.NPComplete.MaximumAreaPolygonalization
