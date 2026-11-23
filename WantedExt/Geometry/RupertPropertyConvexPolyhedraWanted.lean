/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Source record `AMR-071-0085`
# Rupert's property for convex polyhedra

Wikipedia, List of unsolved problems in mathematics (revision 1366636767), Geometry: Rupert's
property.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.LinearAlgebra.Determinant
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Geometry.RupertPropertyConvexPolyhedraWanted

/-- Euclidean `3`-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The orthogonal projection to the first two coordinates. -/
def proj (x : E3) : ℝ × ℝ := (x 0, x 1)

/-- `P` has Rupert's property: for some rotations `Q₁, Q₂` and a translation `t` of the plane, the
shadow of `Q₁ P`, translated by `t`, lies in the interior of the shadow of `Q₂ P` (a hole can be
cut through `P` through which a congruent copy passes). -/
def IsRupert (P : Set E3) : Prop :=
  ∃ (Q₁ Q₂ : E3 ≃ₗᵢ[ℝ] E3) (t : ℝ × ℝ),
    LinearMap.det (Q₁.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 ∧
      LinearMap.det (Q₂.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 ∧
      (fun x => proj (Q₁ x) + t) '' P ⊆ interior ((fun x => proj (Q₂ x)) '' P)

/-- Every convex polyhedron (convex hull of finitely many points with nonempty interior) has
Rupert's property. -/
def conjecture : Prop :=
  ∀ S : Finset E3, (interior (convexHull ℝ (S : Set E3))).Nonempty → IsRupert (convexHull ℝ ↑S)

-- Carried source audit `AMR-071-0085` (see the Moved/ record).

/--
Resolved false: Refuted. Steininger and Yurkevich (arXiv:2508.18475, v2 January 2026,
computer-assisted) prove that the Noperthedron, a point-symmetric convex polyhedron with 90
vertices, is not Rupert (Theorem 1). Their Definition 3 ranges over all pairs of orthogonal
projections and in-plane rotations without a translation, which for point-symmetric polyhedra is
equivalent to the definition with a translation used here, so the Noperthedron refutes the
target. Later work cites it as resolving the Jerrard–Wetzel–Yuan conjecture (Zeng,
arXiv:2604.26531). Source: J. Steininger, S. Yurkevich, A convex polyhedron without Rupert's
property, arXiv:2508.18475 (2025, v2 2026), https://arxiv.org/abs/2508.18475; T. Zeng, A
stellated tetrahedron that is probably not Rupert, arXiv:2604.26531 (2026),
https://arxiv.org/abs/2604.26531. Moved from
`OpenConjectures/Geometry/RupertPropertyConvexPolyhedra`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Geometry.RupertPropertyConvexPolyhedraWanted
