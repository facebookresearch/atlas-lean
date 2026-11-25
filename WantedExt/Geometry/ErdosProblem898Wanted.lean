/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 898
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Geometry.TwoD
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.AffineSpace.Independent

@[expose] public section

open Affine EuclideanGeometry
open scoped EuclideanGeometry EuclideanSpace

namespace MathlibExt.Geometry.ErdosProblem898Wanted

/-! Source record `FC-ErdosProblem898`, ported from FormalConjectures
`ErdosProblems/898.lean` (`theorem erdos_898`) and checked against
erdosproblems.com/898. `ℝ²` is MathlibExt's notation; affine lines,
independence, convex hulls, and orthogonality are Mathlib's. The
`answer(...)` wrapper is elaborated away. Status: resolved true externally by
Mordell and Barrow. This module states the inequality but does not prove it;
a pinned external Lean proof is linked in the registry. -/

/-- **Statement of the Erdős–Mordell inequality.** Writing $XY$ for the distance between points
$X$ and $Y$, this is the assertion that for all affinely independent points $A$, $B$, $C$ of the
Euclidean plane, every point $P$ in the interior of the triangle $ABC$, and all points $M$, $N$,
$L$ on the lines $BC$, $AB$, $CA$ such that the lines $PM$, $PN$, $PL$ are perpendicular to $BC$,
$AB$, $CA$ respectively, we have $PA + PB + PC \ge 2(PM + PN + PL)$. -/
def conjecture : Prop :=
  ∀ (A B C P L M N : ℝ²) (_hABC : AffineIndependent ℝ ![A, B, C])
    (_hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²)))
    (_hN : N ∈ line[ℝ, A, B])
    (_hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction)
    (_hM : M ∈ line[ℝ, B, C])
    (_hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction)
    (_hL : L ∈ line[ℝ, C, A])
    (_hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction),
    dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)

/--
**Erdős–Mordell inequality.** Let $A$, $B$, $C$ be affinely independent points of the Euclidean
plane and $P$ a point in the interior of the triangle $ABC$. Let $M$, $N$, $L$ be points on the
lines $BC$, $AB$, $CA$ such that $PM \perp BC$, $PN \perp AB$ and $PL \perp CA$. Then, writing
$XY$ for the distance between points $X$ and $Y$, we have $PA + PB + PC \ge 2(PM + PN + PL)$.

Source: Paul
Erdős, L. J. Mordell, and David F. Barrow, Problem 3740, American Mathematical Monthly 44
(1937), 252–254, https://doi.org/10.2307/2300713. Moved from
`OpenConjectures/Geometry/ErdosProblem898`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Geometry.ErdosProblem898Wanted
