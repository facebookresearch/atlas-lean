/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeIntegralCurve
public import Mathlib.Algebra.Order.Field.Rat

/-! Tests for `MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeIntegralCurve`. -/

@[expose] public section

open AlgebraicGeometry

namespace ProjectiveSchemeIntegralCurveTest

#check @WeierstrassCurve.dense_range_affineChart
#check @WeierstrassCurve.isIntegral_isProper_dim_one_dense_affineChart

/-- The curve `y² + y = x³ - x` over `ℚ` is an integral proper curve with dense affine chart. -/
example : IsIntegral (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℚ).ProjectiveScheme ∧
    IsProper (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℚ).projectiveSchemeToSpec ∧
    topologicalKrullDim (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℚ).ProjectiveScheme = 1 ∧
    Dense (Set.range (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℚ).affineChart.base) :=
  WeierstrassCurve.isIntegral_isProper_dim_one_dense_affineChart _

end ProjectiveSchemeIntegralCurveTest
