/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.InvariantDifferentialChartAtInfinity

/-!
# Tests for the overlap calculation for the invariant differential at infinity

Examples on the curve `y² + y = x³ - x` over `ℚ`, whose discriminant is `37`.
-/

@[expose] public section

namespace WeierstrassCurve.InvariantDifferentialChartAtInfinityTest

open KaehlerDifferential

/-- The curve `y² + y = x³ - x` over `ℚ`. -/
abbrev E : WeierstrassCurve ℚ := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -1, a₆ := 0 }

theorem E_Δ : E.Δ = 37 := by
  simp [Δ, b₂, b₄, b₆, b₈]
  norm_num

/-- On this curve `h_w = 1 + 2 w + 2 z w`. -/
example : MvPolynomial.pderiv 1 E.polynomialAtInfinity =
    1 + 2 * MvPolynomial.X 1 + 2 * MvPolynomial.X 0 * MvPolynomial.X 1 := by
  rw [pderiv_one_polynomialAtInfinity]
  simp [polynomialAtInfinityW]

/-- On `y² + y = x³ - x`, exactly one form on the overlap of the charts satisfies `P θ = dx` and
`Q θ = dy`. -/
example : ∃! θ : KaehlerDifferential ℚ E.AtInfinityAwayW,
    (2 * E.affineToOverlap E.affineY + algebraMap ℚ _ E.a₁ * E.affineToOverlap E.affineX +
        algebraMap ℚ _ E.a₃) • θ = D ℚ _ (E.affineToOverlap E.affineX) ∧
      (3 * E.affineToOverlap E.affineX ^ 2 +
        2 * algebraMap ℚ _ E.a₂ * E.affineToOverlap E.affineX + algebraMap ℚ _ E.a₄ -
        algebraMap ℚ _ E.a₁ * E.affineToOverlap E.affineY) • θ =
        D ℚ _ (E.affineToOverlap E.affineY) :=
  E.existsUnique_invariantDifferential_atInfinity (by rw [E_Δ]; norm_num)

/-- On this curve, the form on the overlap of the charts with `P θ = dx` and `Q θ = dy` satisfies
`h_w θ = -dz` and `h_z θ = dw`. -/
example : ∃ θ : KaehlerDifferential ℚ E.AtInfinityAwayW,
    algebraMap _ E.AtInfinityAwayW E.partialWAtInfinity • θ =
        -D ℚ _ (algebraMap _ E.AtInfinityAwayW E.zAtInfinity) ∧
      algebraMap _ E.AtInfinityAwayW E.partialZAtInfinity • θ =
        D ℚ _ (algebraMap _ E.AtInfinityAwayW E.wAtInfinity) := by
  have hΔ : E.Δ ≠ 0 := by rw [E_Δ]; norm_num
  obtain ⟨θ, ⟨hP, hQ⟩, -⟩ := E.existsUnique_invariantDifferential_atInfinity hΔ
  exact ⟨θ, E.invariantDifferential_atInfinity hΔ θ hP hQ⟩

end WeierstrassCurve.InvariantDifferentialChartAtInfinityTest
