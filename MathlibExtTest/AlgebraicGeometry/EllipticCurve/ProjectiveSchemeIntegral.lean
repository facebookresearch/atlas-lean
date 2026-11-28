/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeIntegral

/-! Tests for `MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeIntegral`. -/

@[expose] public section

open AlgebraicGeometry

#check @WeierstrassCurve.bijective_algebraMap_gradeZero
#check @WeierstrassCurve.gradeZeroEquiv
#check @WeierstrassCurve.finiteType_gradeZero
#check @WeierstrassCurve.isProper_projectiveSchemeToSpec
#check @WeierstrassCurve.projectiveCoordinate_one_ne_zero
#check @WeierstrassCurve.exists_ne_zero_of_pos
#check @WeierstrassCurve.isIntegral_projectiveScheme
#check @WeierstrassCurve.isIntegral_projectiveScheme_of_field

/-- `y² = x³ + 1` over `ℤ`: the structure morphism is proper. -/
example : IsProper (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℤ).projectiveSchemeToSpec :=
  inferInstance

/-- `y² = x³ + 1` over `ℤ` (a factorial domain): the projective scheme is integral. -/
example : IsIntegral (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℤ).ProjectiveScheme :=
  WeierstrassCurve.isIntegral_projectiveScheme _

/-- The cuspidal cubic `y² = x³` over `ℚ` (discriminant `0`) is still integral. -/
example : IsIntegral (⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve ℚ).ProjectiveScheme :=
  inferInstance

/-- Over `ℤ ⧸ 4` (not a domain) the structure morphism is still proper. -/
example : IsProper (⟨1, 0, 0, 0, 1⟩ : WeierstrassCurve (ZMod 4)).projectiveSchemeToSpec :=
  inferInstance

#check @WeierstrassCurve.X_two_not_mem_span
#check @WeierstrassCurve.isPrime_span_X_zero_X_two
#check @WeierstrassCurve.X_one_not_mem_span_X_zero_X_two
#check @WeierstrassCurve.polynomial_mem_span_X_zero_X_two
#check @WeierstrassCurve.yzHom
#check @WeierstrassCurve.isIntegral_X0
#check @WeierstrassCurve.isIntegral_mk
#check @WeierstrassCurve.ringKrullDim_le
#check @WeierstrassCurve.pointO
#check @WeierstrassCurve.botPoint_lt_pointO
#check @WeierstrassCurve.topologicalKrullDim_projectiveScheme

/-- `y² + y = x³ - x` over `ℚ` is a curve: its projective scheme has dimension `1`. -/
example : topologicalKrullDim (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℚ).ProjectiveScheme = 1 :=
  WeierstrassCurve.topologicalKrullDim_projectiveScheme _

/-- Over `ℤ`, `dim S_W ≤ dim ℤ + 2`. -/
example : ringKrullDim (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℤ).HomogeneousCoordinateRing ≤
    ringKrullDim ℤ + 2 :=
  WeierstrassCurve.ringKrullDim_le _
