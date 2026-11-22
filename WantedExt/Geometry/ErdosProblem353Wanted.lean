/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 353
-/
module

public import MathlibExt.Geometry.TwoD
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Set.Card
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Batteries.Util.ProofWanted

@[expose] public section

open EuclideanGeometry MeasureTheory
open scoped EuclideanSpace

namespace MathlibExt.Geometry.ErdosProblem353Wanted

/-! Source record `FC-ErdosProblem353`, ported from FormalConjectures
`ErdosProblems/353.lean` (`theorem erdos_353` and its four variants) and
checked against erdosproblems.com/353. `IsIsoscelesTrapezoid`,
`IsRightAngled`, `IsCcwConvexPolygon` (in `EuclideanGeometry`) and
`IsIsosceles` (root) are MathlibExt's; `Cospherical`, `volume`,
`convexHull` are Mathlib's. The parent tip's `IsRightAngled` adds pairwise
distinctness, which follows here from the area-1 hypothesis, so the variant
is unchanged in meaning. The `answer(True)` wrapper is elaborated to a
direct proposition. Status: resolved true (Koizumi [Ko25];
cyclic-quadrilateral and congruent-sides variants by Kovač–Predojević
[KoPr24]). The negative congruent-sides result is documented but not
formalized as an unproved declaration. -/

/-- Infinite-measure sets contain area-1 isosceles trapezoids. -/
def conjecture : Prop :=
  ∀ A : Set ℝ², MeasurableSet A → volume A = ⊤ →
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ d ∈ A,
      IsIsoscelesTrapezoid a b c d ∧
      volume (convexHull ℝ {a, b, c, d}) = 1

/-- Infinite-measure sets contain area-1 isosceles triangles. -/
def isoscelesTriangle : Prop :=
  ∀ A : Set ℝ², MeasurableSet A → volume A = ⊤ →
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
      IsIsosceles a b c ∧
      volume (convexHull ℝ {a, b, c}) = 1

/-- Infinite-measure sets contain area-1 right-angled triangles. -/
def rightAngledTriangle : Prop :=
  ∀ A : Set ℝ², MeasurableSet A → volume A = ⊤ →
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
      IsRightAngled a b c ∧
      volume (convexHull ℝ {a, b, c}) = 1

/-- Infinite-measure sets contain area-1 cyclic quadrilaterals. -/
def cyclicQuadrilateral : Prop :=
  ∀ A : Set ℝ², MeasurableSet A → volume A = ⊤ →
    ∃ Q : Set ℝ², Q ⊆ A ∧ Q.ncard = 4 ∧ Cospherical Q ∧
      volume (convexHull ℝ Q) = 1

/--
Resolved true: Every formalized target is proved. Koizumi (arXiv:2501.01914, Proc. Amer. Math.
Soc.) proved that every measurable planar set of infinite measure contains the vertices of an
isosceles trapezoid, an isosceles triangle, and a right-angled triangle of area 1; Kovač and
Predojević (arXiv:2412.11725) proved the cyclic-quadrilateral case. Their negative answer for
convex polygons with congruent sides concerns a source variant that is not formalized here
(erdosproblems.com/353, checked 2026-10-22: proved (Lean)). This target holds: Koizumi
(arXiv:2501.01914): every measurable planar set of infinite measure contains the vertices of an
isosceles trapezoid of area 1. Source: Junnosuke Koizumi, Isosceles trapezoids of unit area with
vertices in sets of infinite planar measure, arXiv:2501.01914 (trapezoid, isosceles-triangle,
and right-triangle parts), Proc. Amer. Math. Soc. 153 (2025), 4753–4758,
https://arxiv.org/abs/2501.01914; Kovač–Predojević [KoPr24], Polygons of unit area with vertices
in sets of infinite planar measure, arXiv:2412.11725 (cyclic-quadrilateral positive and
congruent-sides negative parts), https://arxiv.org/abs/2412.11725. Moved from
`OpenConjectures/Geometry/ErdosProblem353`.
-/
public theorem_wanted conjecture_holds : conjecture

/--
Resolved true: Every formalized target is proved. Koizumi (arXiv:2501.01914, Proc. Amer. Math.
Soc.) proved that every measurable planar set of infinite measure contains the vertices of an
isosceles trapezoid, an isosceles triangle, and a right-angled triangle of area 1; Kovač and
Predojević (arXiv:2412.11725) proved the cyclic-quadrilateral case. Their negative answer for
convex polygons with congruent sides concerns a source variant that is not formalized here
(erdosproblems.com/353, checked 2026-10-22: proved (Lean)). This target holds: Koizumi
(arXiv:2501.01914) gives the affirmative answer for isosceles triangles: such a set contains the
vertices of an isosceles triangle of area 1. Source: Junnosuke Koizumi, Isosceles trapezoids of
unit area with vertices in sets of infinite planar measure, arXiv:2501.01914 (trapezoid,
isosceles-triangle, and right-triangle parts), Proc. Amer. Math. Soc. 153 (2025), 4753–4758,
https://arxiv.org/abs/2501.01914; Kovač–Predojević [KoPr24], Polygons of unit area with vertices
in sets of infinite planar measure, arXiv:2412.11725 (cyclic-quadrilateral positive and
congruent-sides negative parts), https://arxiv.org/abs/2412.11725. Moved from
`OpenConjectures/Geometry/ErdosProblem353`.
-/
public theorem_wanted isoscelesTriangle_holds : isoscelesTriangle

/--
Resolved true: Every formalized target is proved. Koizumi (arXiv:2501.01914, Proc. Amer. Math.
Soc.) proved that every measurable planar set of infinite measure contains the vertices of an
isosceles trapezoid, an isosceles triangle, and a right-angled triangle of area 1; Kovač and
Predojević (arXiv:2412.11725) proved the cyclic-quadrilateral case. Their negative answer for
convex polygons with congruent sides concerns a source variant that is not formalized here
(erdosproblems.com/353, checked 2026-10-22: proved (Lean)). This target holds: Koizumi
(arXiv:2501.01914) gives the affirmative answer for right-angled triangles: such a set contains
the vertices of a right-angled triangle of area 1. Source: Junnosuke Koizumi, Isosceles
trapezoids of unit area with vertices in sets of infinite planar measure, arXiv:2501.01914
(trapezoid, isosceles-triangle, and right-triangle parts), Proc. Amer. Math. Soc. 153 (2025),
4753–4758, https://arxiv.org/abs/2501.01914; Kovač–Predojević [KoPr24], Polygons of unit area
with vertices in sets of infinite planar measure, arXiv:2412.11725 (cyclic-quadrilateral
positive and congruent-sides negative parts), https://arxiv.org/abs/2412.11725. Moved from
`OpenConjectures/Geometry/ErdosProblem353`.
-/
public theorem_wanted rightAngledTriangle_holds : rightAngledTriangle

/--
Resolved true: Every formalized target is proved. Koizumi (arXiv:2501.01914, Proc. Amer. Math.
Soc.) proved that every measurable planar set of infinite measure contains the vertices of an
isosceles trapezoid, an isosceles triangle, and a right-angled triangle of area 1; Kovač and
Predojević (arXiv:2412.11725) proved the cyclic-quadrilateral case. Their negative answer for
convex polygons with congruent sides concerns a source variant that is not formalized here
(erdosproblems.com/353, checked 2026-10-22: proved (Lean)). This target holds: Kovač and
Predojević (arXiv:2412.11725): such a set contains four distinct points on a circle whose
quadrilateral has area 1. Source: Junnosuke Koizumi, Isosceles trapezoids of unit area with
vertices in sets of infinite planar measure, arXiv:2501.01914 (trapezoid, isosceles-triangle,
and right-triangle parts), Proc. Amer. Math. Soc. 153 (2025), 4753–4758,
https://arxiv.org/abs/2501.01914; Kovač–Predojević [KoPr24], Polygons of unit area with vertices
in sets of infinite planar measure, arXiv:2412.11725 (cyclic-quadrilateral positive and
congruent-sides negative parts), https://arxiv.org/abs/2412.11725. Moved from
`OpenConjectures/Geometry/ErdosProblem353`.
-/
public theorem_wanted cyclicQuadrilateral_holds : cyclicQuadrilateral

end MathlibExt.Geometry.ErdosProblem353Wanted
