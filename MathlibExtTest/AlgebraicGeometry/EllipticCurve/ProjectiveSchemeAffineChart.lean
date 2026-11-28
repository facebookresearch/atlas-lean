/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeAffineChart
public import Mathlib.Algebra.Order.Field.Rat

/-! Tests for `MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeAffineChart`. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace ProjectiveSchemeAffineChartTest

#check @WeierstrassCurve.dehomogenizeZ
#check @WeierstrassCurve.dehomogenizeZ_mk
#check @WeierstrassCurve.dehomogenizeZ_algebraMap
#check @WeierstrassCurve.awayZToAffine
#check @WeierstrassCurve.awayZToAffine_mk
#check @WeierstrassCurve.coordinate_relation
#check @WeierstrassCurve.affine_relation_of_mul_eq_one
#check @WeierstrassCurve.affineToAwayZ
#check @WeierstrassCurve.awayZToAffine_comp_affineToAwayZ
#check @WeierstrassCurve.affineToAwayZ_comp_awayZToAffine
#check @WeierstrassCurve.awayZRingEquiv
#check @WeierstrassCurve.affineChart
#check @WeierstrassCurve.opensRange_affineChart
#check @WeierstrassCurve.affineChart_projectiveSchemeToSpec

/-- The curve `y² + y = x³ - x` over `ℚ`. -/
abbrev E : WeierstrassCurve ℚ := ⟨0, 0, 1, -1, 0⟩

/-- `X / Z` corresponds to `x` and `Y / Z` to `y`. -/
example : E.awayZRingEquiv E.xZ = E.affineX ∧ E.awayZRingEquiv E.yZ = E.affineY :=
  ⟨E.awayZRingEquiv_xZ, E.awayZRingEquiv_yZ⟩

example : IsOpenImmersion E.affineChart := inferInstance

/-- Over `ℤ`, the affine chart lies over `Spec ℤ`. -/
example (W : WeierstrassCurve ℤ) :
    W.affineChart ≫ W.projectiveSchemeToSpec =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ W.toAffine.CoordinateRing)) :=
  W.affineChart_projectiveSchemeToSpec

end ProjectiveSchemeAffineChartTest
