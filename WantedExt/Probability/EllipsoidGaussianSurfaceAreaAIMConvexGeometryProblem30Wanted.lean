/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ellipsoids have uniformly bounded Gaussian surface area (AIM algorithmic convex geometry, 11)

AIM workshop Algorithmic convex geometry, problem list, Problem 11 (R. O'Donnell): is it true that
every ellipsoid has Gaussian surface area bounded by a universal constant? (K. Ball: for a general
convex body the answer is `O(n^{1/4})`.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

namespace MathlibExt.Probability.EllipsoidGaussianSurfaceAreaAIMConvexGeometryProblem30Wanted

/-!
Source: AIM workshop Algorithmic convex geometry, problem list,
https://aimath.org/WWN/convexgeometry/convexgeometry.pdf, Problem 11 (R. O'Donnell). UnsolvedMath
record UM-20001298 (`AIM-CONVEX_GEOMETRY-0030`), dataset ulamai/UnsolvedMath v1.8.0.

Gaussian surface area is Kane's `Γ(A) = liminf_{δ → 0} γₙ(A_δ \ A) / δ`, `γₙ` the standard Gaussian
measure on `ℝⁿ` (`stdGaussian`) and `A_δ = {x : d(x, A) ≤ δ}`, valued in `[0, ∞]` so that the liminf
has no junk value. An ellipsoid is `{x : ‖T (x - c)‖ ≤ 1}` with `T` invertible linear, any centre
`c`; it is `{q ≥ 0}` for the degree-2 polynomial `q(x) = 1 - ‖T (x - c)‖²`, i.e. the positive region
of a degree-2 polynomial threshold function. The constant is uniform in `n`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Euclidean space `ℝⁿ`. -/
abbrev En (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The Gaussian surface area `Γ(A) = liminf_{δ → 0⁺} γₙ(A_δ \ A) / δ`, where `γₙ` is the standard
Gaussian measure on `ℝⁿ` and `A_δ = {x | dist(x, A) ≤ δ}` (`Metric.cthickening`), valued in
`[0, ∞]`. -/
noncomputable def gaussianSurfaceArea {n : ℕ} (A : Set (En n)) : ℝ≥0∞ :=
  liminf (fun δ : ℝ => stdGaussian (En n) (Metric.cthickening δ A \ A) / ENNReal.ofReal δ)
    (𝓝[>] (0 : ℝ))

/-- `A` is a (closed, full-dimensional, possibly translated) ellipsoid: `A = {x | ‖T (x - c)‖ ≤ 1}`
for an invertible linear map `T` and a centre `c`. -/
def IsEllipsoid {n : ℕ} (A : Set (En n)) : Prop :=
  ∃ (T : En n ≃L[ℝ] En n) (c : En n), A = {x | ‖T (x - c)‖ ≤ 1}

/-- O'Donnell's question (AIM, Algorithmic convex geometry, Problem 11): the Gaussian surface area
of ellipsoids is bounded by a universal constant, in every dimension. -/
def ellipsoidGaussianSurfaceAreaBounded : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (A : Set (En n)), IsEllipsoid A → gaussianSurfaceArea A ≤ ENNReal.ofReal C

/--
Resolved true: Kane proved that every degree-`d` polynomial threshold function has Gaussian surface
area at most `d / √(2π)` (Theorem 1.2), in every dimension; an ellipsoid `{x : ‖T (x - c)‖ ≤ 1}` is
the region `{q ≥ 0}` of the degree-2 polynomial `q(x) = 1 - ‖T (x - c)‖²`, so its Gaussian surface
area is at most `√(2/π)`. Source: AIM workshop Algorithmic convex geometry, problem list,
https://aimath.org/WWN/convexgeometry/convexgeometry.pdf, Problem 11 (R. O'Donnell); resolution: D.
M. Kane, The Gaussian surface area and noise sensitivity of degree-d polynomial threshold functions,
Comput. Complexity 20 (2011), 389-412 (CCC 2010), Section 1.3 (definition Γ(A) = liminf_{δ→0}
GaussianVolume(A_δ \ A)/δ) and Theorem 1.2: if f is a degree-d polynomial threshold function then
Γ(f) ≤ d/√(2π); for d = 2 this covers every ellipsoid, with constant 2/√(2π) = √(2/π),
https://doi.org/10.1007/s00037-011-0012-6.
-/
public theorem_wanted ellipsoidGaussianSurfaceAreaBounded_holds :
    ellipsoidGaussianSurfaceAreaBounded

end MathlibExt.Probability.EllipsoidGaussianSurfaceAreaAIMConvexGeometryProblem30Wanted
