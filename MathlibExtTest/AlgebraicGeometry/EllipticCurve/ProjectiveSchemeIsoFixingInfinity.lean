/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeIsoFixingInfinity
public import Mathlib.Algebra.Order.Field.Rat

/-! Tests for `MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeIsoFixingInfinity`. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace ProjectiveSchemeIsoFixingInfinityTest

#check @WeierstrassCurve.base_mem_range_zeroSection_iff
#check @WeierstrassCurve.range_affineChart_comp_subset
#check @WeierstrassCurve.zeroSection_comp_inv
#check @WeierstrassCurve.affineChartRestrict
#check @WeierstrassCurve.affineChartRestrict_comp
#check @WeierstrassCurve.affineChartRingEquiv
#check @WeierstrassCurve.specMap_affineChartRingEquiv
#check @WeierstrassCurve.affineChartRingEquiv_algebraMap
#check @WeierstrassCurve.affineChartAlgEquiv
#check @WeierstrassCurve.affineChart_comp_eq

/-- The curve `y² + y = x³ - x` over `ℚ`. -/
abbrev E : WeierstrassCurve ℚ := ⟨0, 0, 1, -1, 0⟩

/-- The identity of the projective curve of `E` restricts to an automorphism of `A_E`. -/
example : E.affineChart ≫ 𝟙 E.ProjectiveScheme =
    Spec.map (CommRingCat.ofHom (WeierstrassCurve.affineChartAlgEquiv (𝟙 E.ProjectiveScheme)
      (Category.comp_id _) (Category.id_comp _) :
        E.toAffine.CoordinateRing →+* E.toAffine.CoordinateRing)) ≫ E.affineChart :=
  WeierstrassCurve.affineChart_comp_eq _ _ _

end ProjectiveSchemeIsoFixingInfinityTest
