/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeChartAtInfinity

/-!
# Tests for the chart at infinity of the projective Weierstrass scheme
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace WeierstrassCurve.ProjectiveSchemeChartAtInfinityTest

#check @WeierstrassCurve.aeval_polynomialAtInfinity_mul
#check @WeierstrassCurve.dehomogenizeY
#check @WeierstrassCurve.dehomogenizeY_polynomial
#check @WeierstrassCurve.homogeneousToAtInfinity
#check @WeierstrassCurve.homogeneousToAtInfinity_mk
#check @WeierstrassCurve.homogeneousToAtInfinity_projectiveCoordinate_one
#check @WeierstrassCurve.projectiveCoordinate_mem_one_smul
#check @WeierstrassCurve.xOverY
#check @WeierstrassCurve.zOverY
#check @WeierstrassCurve.awayYAlgebraMap
#check @WeierstrassCurve.awayYDehomogenize
#check @WeierstrassCurve.awayYDehomogenize_mk
#check @WeierstrassCurve.eval₂Hom_polynomialAtInfinity
#check @WeierstrassCurve.awayYHomogenize
#check @WeierstrassCurve.awayYHomogenize_zAtInfinity
#check @WeierstrassCurve.awayYHomogenize_wAtInfinity
#check @WeierstrassCurve.awayYHomogenize_algebraMap
#check @WeierstrassCurve.awayYDehomogenize_awayYAlgebraMap
#check @WeierstrassCurve.awayYDehomogenize_xOverY
#check @WeierstrassCurve.awayYDehomogenize_zOverY
#check @WeierstrassCurve.awayYDehomogenize_comp_awayYHomogenize
#check @WeierstrassCurve.awayYHomogenize_comp_awayYDehomogenize
#check @WeierstrassCurve.awayYRingEquiv
#check @WeierstrassCurve.awayYRingEquiv_mk
#check @WeierstrassCurve.awayYRingEquiv_xOverY
#check @WeierstrassCurve.awayYRingEquiv_zOverY
#check @WeierstrassCurve.awayYRingEquiv_symm_zAtInfinity
#check @WeierstrassCurve.awayYRingEquiv_symm_wAtInfinity
#check @WeierstrassCurve.awayYRingEquiv_algebraMap
#check @WeierstrassCurve.chartAtInfinity
#check @WeierstrassCurve.isOpenImmersion_chartAtInfinity
#check @WeierstrassCurve.opensRange_chartAtInfinity
#check @WeierstrassCurve.chartAtInfinity_projectiveSchemeToSpec
#check @WeierstrassCurve.zeroSection
#check @WeierstrassCurve.zeroSection_projectiveSchemeToSpec

/-- The curve `y² + y = x³ - x` over `ℤ`, with `a₃ = 1`, `a₄ = -1`. -/
def W₀ : WeierstrassCurve ℤ := ⟨0, 0, 1, -1, 0⟩

/-- Over `ℤ`, the chart at infinity of `y² + y = x³ - x` is an open immersion. -/
example : IsOpenImmersion W₀.chartAtInfinity := inferInstance

/-- Over `ℤ`, its image is `D₊(Y)`. -/
example : W₀.chartAtInfinity.opensRange =
    Proj.basicOpen W₀.projectiveGrading (W₀.projectiveCoordinate 1) :=
  W₀.opensRange_chartAtInfinity

/-- Over `ℤ`, the zero section is a section of the structure morphism. -/
example : W₀.zeroSection ≫ W₀.projectiveSchemeToSpec = 𝟙 _ :=
  W₀.zeroSection_projectiveSchemeToSpec

/-- Over `ℚ`, the dehomogenization sends `X / Y` to `z` and its inverse sends `w` to `Z / Y`. -/
example (W : WeierstrassCurve ℚ) :
    W.awayYRingEquiv W.xOverY = W.zAtInfinity ∧ W.awayYRingEquiv.symm W.wAtInfinity = W.zOverY :=
  ⟨W.awayYRingEquiv_xOverY, W.awayYRingEquiv_symm_wAtInfinity⟩

/-- The zero section followed by the structure morphism is the identity, over `ZMod 5`. -/
example (W : WeierstrassCurve (ZMod 5)) :
    W.zeroSection ≫ W.projectiveSchemeToSpec = 𝟙 (Spec (CommRingCat.of (ZMod 5))) :=
  W.zeroSection_projectiveSchemeToSpec

end WeierstrassCurve.ProjectiveSchemeChartAtInfinityTest
