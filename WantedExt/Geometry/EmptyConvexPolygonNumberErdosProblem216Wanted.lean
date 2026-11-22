/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Empty convex polygons in planar point sets (Erdős Problem 216)

Erdős Problem 216: let `g(k)` be the least integer, if any, such that any `g(k)` points in `ℝ²`
contain an empty convex `k`-gon (one with no point of the set in its interior). Does `g(k)` exist?
If so, estimate `g(k)`.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Geometry.TwoD

@[expose] public section

namespace MathlibExt.Geometry.EmptyConvexPolygonNumberErdosProblem216Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #216, https://www.erdosproblems.com/216 (status
DISPROVED). UnsolvedMath record UM-30006771 (`EP-216`), dataset ulamai/UnsolvedMath v1.8.0.

Point sets are in general position (no three collinear, the canonical
`EuclideanGeometry.NonTrilinear`), as in Heule and Scheucher's statement of the problem (§1), where
`h(3) = 3`, `h(4) = 5` and `h(5) = 10` are recorded for such sets. An empty convex `k`-gon of `s` is
a `k`-subset with no point in the convex hull of the others and no point of `s` in the interior of
its convex hull. `g(k)` exists when some `N` works for every set of at least `N` points; this equals
the condition for sets of exactly `N` points, since sweeping a line in a generic direction gives an
`N`-subset whose convex hull contains no other point. There are two targets: `3 ≤ k ≤ 6` (exists)
and `k ≥ 7` (stated for some `k ≥ 7`, refuted for all). The estimates of `g(k)` are not formalized.
-/

/-- `t ⊆ s` is an empty convex `k`-gon of `s`: `t` has `k` points, none in the convex hull of the
others, and no point of `s` lies in the interior of the convex hull of `t`. -/
def IsEmptyConvexPolygon (s t : Finset (EuclideanSpace ℝ (Fin 2))) (k : ℕ) : Prop :=
  t ⊆ s ∧ t.card = k ∧
    (∀ p ∈ t, p ∉ convexHull ℝ ((t.erase p : Finset _) : Set (EuclideanSpace ℝ (Fin 2)))) ∧
    ∀ p ∈ s, p ∉ interior (convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 2))))

/-- `g(k)` exists: for some `N`, every set of at least `N` points of `ℝ²` in general position (no
three collinear, `EuclideanGeometry.NonTrilinear`) contains an empty convex `k`-gon. -/
def EmptyConvexPolygonNumberExists (k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ s : Finset (EuclideanSpace ℝ (Fin 2)), N ≤ s.card →
    EuclideanGeometry.NonTrilinear (s : Set (EuclideanSpace ℝ (Fin 2))) →
    ∃ t, IsEmptyConvexPolygon s t k

/-- Erdős Problem 216, `k ≤ 6`: `g(k)` exists for `3 ≤ k ≤ 6`. -/
def emptyConvexPolygonNumberExistsUpToSix : Prop :=
  ∀ k : ℕ, 3 ≤ k → k ≤ 6 → EmptyConvexPolygonNumberExists k

/-- Erdős Problem 216, `k ≥ 7`, stated for some `k ≥ 7`: `g(k)` exists. -/
def emptyConvexPolygonNumberExistsFromSeven : Prop :=
  ∃ k : ℕ, 7 ≤ k ∧ EmptyConvexPolygonNumberExists k

/--
Resolved true: `g(3) = 3` and `g(4) = 5`, Harborth proved `g(5) = 10`, and Nicolás and Gerken
independently proved that `g(6)` exists; Heule and Scheucher record these values for points in
general position (§1) and proved `g(6) = 30` (Theorem 1). Source: T. F. Bloom, Erdős Problems,
Problem #216, https://www.erdosproblems.com/216 (status DISPROVED); resolution: J. D. Horton, Sets
with no empty convex 7-gons, Canad. Math. Bull. 26 (1983), 482-484; H. Harborth, Konvexe Fünfecke in
ebenen Punktmengen, Elem. Math. 33 (1978), 116-118; C. M. Nicolás, The empty hexagon theorem,
Discrete Comput. Geom. 38 (2007), 389-397; T. Gerken, Empty convex hexagons in planar point sets,
Discrete Comput. Geom. 39 (2008), 239-272; M. J. H. Heule and M. Scheucher, Happy Ending: An Empty
Hexagon in Every Set of 30 Points, TACAS 2024, Lecture Notes in Comput. Sci., Springer (2024),
61-80, arXiv:2403.00737, erdosproblems.com/216: g(4) = 5, g(5) = 10 (Harborth), g(6) exists
(Nicolás, Gerken; g(6) = 30 by Heule-Scheucher), g(k) does not exist for k ≥ 7 (Horton);
Heule-Scheucher §1: h(3) = 3, h(4) = 5, h(5) = 10 for points in general position, and Theorem 1:
h(6) = 30, https://doi.org/10.4153/CMB-1983-077-8.
-/
public theorem_wanted emptyConvexPolygonNumberExistsUpToSix_holds :
    emptyConvexPolygonNumberExistsUpToSix

/--
Resolved false: Horton constructed arbitrarily large sets in general position with no empty convex
`7`-gon, and erdosproblems.com/216 records that `g(k)` exists for no `k ≥ 7`; the site lists the
problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem #216,
https://www.erdosproblems.com/216 (status DISPROVED); resolution: J. D. Horton, Sets with no empty
convex 7-gons, Canad. Math. Bull. 26 (1983), 482-484; H. Harborth, Konvexe Fünfecke in ebenen
Punktmengen, Elem. Math. 33 (1978), 116-118; C. M. Nicolás, The empty hexagon theorem, Discrete
Comput. Geom. 38 (2007), 389-397; T. Gerken, Empty convex hexagons in planar point sets, Discrete
Comput. Geom. 39 (2008), 239-272; M. J. H. Heule and M. Scheucher, Happy Ending: An Empty Hexagon in
Every Set of 30 Points, TACAS 2024, Lecture Notes in Comput. Sci., Springer (2024), 61-80,
arXiv:2403.00737, erdosproblems.com/216: g(4) = 5, g(5) = 10 (Harborth), g(6) exists (Nicolás,
Gerken; g(6) = 30 by Heule-Scheucher), g(k) does not exist for k ≥ 7 (Horton); Heule-Scheucher §1:
h(3) = 3, h(4) = 5, h(5) = 10 for points in general position, and Theorem 1: h(6) = 30,
https://doi.org/10.4153/CMB-1983-077-8.
-/
public theorem_wanted emptyConvexPolygonNumberExistsFromSeven_refuted :
    ¬ emptyConvexPolygonNumberExistsFromSeven

end MathlibExt.Geometry.EmptyConvexPolygonNumberErdosProblem216Wanted
