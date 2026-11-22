/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Distinct distances among the vertices of a convex polygon (Erdős Problem 93)

Erdős Problem 93: if `n` distinct points in `ℝ²` form a convex polygon then they determine at least
`⌊n/2⌋` distinct distances.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Independent
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Geometry.Metric

@[expose] public section

namespace MathlibExt.Geometry.ConvexPolygonDistinctDistancesErdosProblem93Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #93, https://www.erdosproblems.com/93 (status PROVED
(LEAN)). UnsolvedMath record UM-30006718 (`EP-93`), dataset ulamai/UnsolvedMath v1.8.0.

Points of `EuclideanSpace ℝ (Fin 2)`; forming a convex polygon is convex position,
`ConvexIndependent ℝ` (no point is in the convex hull of the others, so no three are collinear). The
number of distinct distances is MathlibExt's `distinctDistances` (values `dist x y` over pairs `x ≠
y`), and `⌊n/2⌋` is `A.card / 2` in `ℕ`. Compared with the formal-conjectures statement
`ErdosProblems/93.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 93: `n` points of the plane forming a convex polygon (in convex position: none
lies in the convex hull of the others) determine at least `⌊n / 2⌋` distinct distances
(`distinctDistances`, MathlibExt). -/
def convexPositionDistinctDistances : Prop :=
  ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
    ConvexIndependent ℝ (fun x : A => (x : EuclideanSpace ℝ (Fin 2))) →
      A.card / 2 ≤ distinctDistances A

/--
Resolved true: Altman proved that the vertices of a convex `n`-gon determine at least `⌊n/2⌋`
distinct distances; erdosproblems.com/93 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #93, https://www.erdosproblems.com/93 (status PROVED (LEAN)); resolution: E.
Altman, On a problem of P. Erdős, Amer. Math. Monthly (1963), 148-157, erdosproblems.com/93: 'Solved
by Altman', https://www.erdosproblems.com/93.
-/
public theorem_wanted convexPositionDistinctDistances_holds : convexPositionDistinctDistances

end MathlibExt.Geometry.ConvexPolygonDistinctDistancesErdosProblem93Wanted
