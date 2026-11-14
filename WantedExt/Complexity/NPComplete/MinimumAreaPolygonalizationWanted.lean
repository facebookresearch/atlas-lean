/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM AREA POLYGONALIZATION is NP-complete

Source:
S. P. Fekete, "On simple polygonalizations with optimal area", Discrete and Computational
Geometry 23(1) (2000), 73-110, doi:10.1007/PL00009492.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Logic.Equiv.Fin.Rotate
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.QuadraticProgrammingWanted
public import WantedExt.Geometry.SegmentVisibilityShared

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumAreaPolygonalization

open MetaMathlibExt.Complexity.NPComplete.QuadraticProgramming (RatCode ratVal)

/-!
# MINIMUM AREA POLYGONALIZATION is NP-complete

INSTANCE: a finite set `S` of points in the plane with integer coordinates, and a rational `A`.
QUESTION: is there a simple polygon with vertex set exactly `S` and area at most `A`?

This is the decision version of Fekete's MIN-AREA ("Given a finite set P of points in the
Euclidean plane. Among all the simple polygons with vertex set P, find one with minimal
enclosed area") for points of the integer grid, the setting of Fekete's proof: his Theorem 3.1
shows that it is NP-complete to decide whether `n` grid points have a simple polygon of area
`n/2 - 1`, the least possible area by Pick's theorem.

A polygon with vertex set exactly `S = {p₀, …, p_{n-1}}` is given by a cyclic order of the
points: a permutation `σ` of the indices, visiting `p_{σ 0}, p_{σ 1}, …, p_{σ (n-1)}` and back
to `p_{σ 0}` (Mathlib's `finRotate` gives the next index). It is simple in the sense of the
shared `MathlibExt.Geometry.SegmentVisibilityShared.IsSimplePolygon`: at least three vertices,
nondegenerate edges, and edges (closed segments in the real plane) meeting only at the common
vertex of consecutive edges. Consecutive edges may be collinear (a straight angle). The enclosed
area of a simple polygon is `|∑ⱼ (xⱼ yⱼ₊₁ - xⱼ₊₁ yⱼ)| / 2` (the shoelace formula, indices mod
`n`), which is used as the definition of its area.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. An integer coordinate is a pair
`(p, q)` of naturals standing for `p - q`, and `A` is a rational `(p - q) / r` given as
`((p, q), r)` (`QuadraticProgramming.RatCode`) with `0 < r`.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the points of `S`, each a pair of integer coordinates given as
(positive part, negative part) pairs, and the bound `A`. -/
abbrev MinimumAreaPolygonalizationInstance := List ((ℕ × ℕ) × (ℕ × ℕ)) × RatCode

/-- The integer coordinates of the `k`-th listed point. -/
def coord (i : MinimumAreaPolygonalizationInstance) (k : Fin i.1.length) : ℤ × ℤ :=
  ((i.1[k].1.1 : ℤ) - i.1[k].1.2, (i.1[k].2.1 : ℤ) - i.1[k].2.2)

/-- The `k`-th listed point in the real plane. -/
noncomputable def point (i : MinimumAreaPolygonalizationInstance) (k : Fin i.1.length) :
    ℝ × ℝ :=
  ((coord i k).1, (coord i k).2)

/-- Well-formedness of an instance: the listed points are pairwise distinct (each point of `S`
is listed once), and the denominator of `A` is positive. -/
def WellFormed (i : MinimumAreaPolygonalizationInstance) : Prop :=
  Function.Injective (coord i) ∧ 0 < i.2.2

/-- Twice the signed area of the polygon through the points in the cyclic order `σ` (shoelace
formula): `∑ⱼ (xⱼ yⱼ₊₁ - xⱼ₊₁ yⱼ)` over the vertices `p_{σ j}`, indices mod `n`. -/
def twiceSignedArea (i : MinimumAreaPolygonalizationInstance)
    (σ : Equiv.Perm (Fin i.1.length)) : ℤ :=
  ∑ j, ((coord i (σ j)).1 * (coord i (σ (finRotate _ j))).2 -
    (coord i (σ (finRotate _ j))).1 * (coord i (σ j)).2)

/-- Some simple polygon with vertex set exactly `S` has area at most `A`: some cyclic order `σ`
of the points gives a simple polygon `p_{σ 0}, …, p_{σ (n-1)}` whose shoelace area is at most
`A`. -/
def MinimumAreaPolygonalizationFeasible (i : MinimumAreaPolygonalizationInstance) : Prop :=
  ∃ σ : Equiv.Perm (Fin i.1.length),
    MathlibExt.Geometry.SegmentVisibilityShared.IsSimplePolygon (point i ∘ σ) ∧
      (|twiceSignedArea i σ| : ℚ) / 2 ≤ ratVal i.2

open Classical in
/-- MINIMUM AREA POLYGONALIZATION as a decision problem over bitstrings. -/
noncomputable def minimumAreaPolygonalizationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumAreaPolygonalizationInstance) x with
  | some i => decide (WellFormed i ∧ MinimumAreaPolygonalizationFeasible i)
  | none => false

/-- **MINIMUM AREA POLYGONALIZATION is NP-complete.** Source: Fekete (2000), Theorem 3.1. -/
public theorem_wanted minimumAreaPolygonalization_npComplete :
    minimumAreaPolygonalizationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumAreaPolygonalizationDec

end MetaMathlibExt.Complexity.NPComplete.MinimumAreaPolygonalization
