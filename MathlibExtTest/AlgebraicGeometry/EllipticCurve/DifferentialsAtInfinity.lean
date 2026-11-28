/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.EllipticCurve.DifferentialsAtInfinity

/-!
# Tests for the differentials of the chart at infinity

Concrete checks on the curve `y² + y = x³ - x` over `ℚ`, whose polynomial at infinity is
`h = w + w² - z³ + z w²`, with `h_z = -3 z² + w²` and `h_w = 1 + 2 w + 2 z w`.
-/

open MvPolynomial KaehlerDifferential WeierstrassCurve

namespace DifferentialsAtInfinityTest

/-- The curve `y² + y = x³ - x` over `ℚ`. -/
noncomputable abbrev E : WeierstrassCurve ℚ := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -1, a₆ := 0 }

/-- Its partial derivative `h_z` is `-3 z² + w²`. -/
example : E.polynomialAtInfinityZ = -3 * X 0 ^ 2 + X 1 ^ 2 := by
  simp [polynomialAtInfinityZ]

/-- Its partial derivative `h_w` is `1 + 2 w + 2 z w`. -/
example : E.polynomialAtInfinityW = 1 + 2 * X 1 + 2 * X 0 * X 1 := by
  simp [polynomialAtInfinityW]

/-- `h_w(0, 0) = 1`, read from the general statement. -/
example : eval 0 E.polynomialAtInfinityW = 1 := E.eval_zero_polynomialAtInfinityW

/-- `h_w(0, 0) = 1`, checked by direct evaluation. -/
example : eval 0 (1 + 2 * X 1 + 2 * X 0 * X 1 : MvPolynomial (Fin 2) ℚ) = 1 := by
  simp

/-- `h_w` maps to `1` under evaluation of `B_E` at the point at infinity. -/
example : E.evalAtInfinity E.partialWAtInfinity = 1 :=
  E.evalAtInfinity_partialWAtInfinity

/-- The relation `h_z dz + h_w dw = 0` in `Ω¹_{B_E/ℚ}`. -/
example : E.partialZAtInfinity • D ℚ _ E.zAtInfinity + E.partialWAtInfinity • D ℚ _ E.wAtInfinity =
    0 :=
  E.relation_D_atInfinity

/-- `dw = -(h_z / h_w) dz` in `Ω¹_{S/ℚ}`. -/
example : D ℚ _ (algebraMap _ E.AwayPartialW E.wAtInfinity) =
    -(algebraMap _ E.AwayPartialW E.partialZAtInfinity *
        IsLocalization.Away.invSelf E.partialWAtInfinity) •
      D ℚ _ (algebraMap _ E.AwayPartialW E.zAtInfinity) :=
  E.D_wAtInfinity_awayPartialW

/-- The basis vector of `Ω¹_{S/ℚ}` is `dz`. -/
example : E.basisAwayPartialW 0 = D ℚ _ (algebraMap _ E.AwayPartialW E.zAtInfinity) :=
  E.basisAwayPartialW_apply 0

/-- `Ω¹_{S/ℚ}` is free, found by instance search. -/
example : Module.Free E.AwayPartialW (KaehlerDifferential ℚ E.AwayPartialW) := inferInstance

/-- `S` is nontrivial, found by instance search. -/
example : Nontrivial E.AwayPartialW := inferInstance

/-- `Ω¹_{S/ℚ}` has rank one. -/
example : Module.finrank E.AwayPartialW (KaehlerDifferential ℚ E.AwayPartialW) = 1 :=
  E.finrank_awayPartialW

/-- The rank-one statement also holds over `ℤ`, with no field hypothesis. -/
example (W : WeierstrassCurve ℤ) :
    Module.finrank W.AwayPartialW (KaehlerDifferential ℤ W.AwayPartialW) = 1 :=
  W.finrank_awayPartialW

/-- Every differential of `S` is a multiple of `dz`. -/
example (ω : KaehlerDifferential ℚ E.AwayPartialW) :
    ω ∈ Submodule.span E.AwayPartialW {D ℚ _ (algebraMap _ E.AwayPartialW E.zAtInfinity)} := by
  rw [E.span_D_zAtInfinity_awayPartialW]
  exact Submodule.mem_top

end DifferentialsAtInfinityTest
