/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveScheme
public import Mathlib.Algebra.Order.Field.Rat

/-! Tests for `MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveScheme`. -/

@[expose] public section

open AlgebraicGeometry

namespace ProjectiveSchemeTest

#check @WeierstrassCurve.HomogeneousCoordinateRing
#check @WeierstrassCurve.isHomogeneous_span_polynomial
#check @WeierstrassCurve.projectiveGrading
#check @WeierstrassCurve.mk_mem_projectiveGrading
#check @WeierstrassCurve.projectiveCoordinate
#check @WeierstrassCurve.projectiveCoordinate_mem
#check @WeierstrassCurve.ProjectiveScheme
#check @WeierstrassCurve.projectiveSchemeToSpec

/-- The curve `y² + y = x³ - x` over `ℚ`. -/
abbrev E : WeierstrassCurve ℚ := ⟨0, 0, 1, -1, 0⟩

/-- `Z` has degree `1` in the homogeneous coordinate ring of `E`. -/
example : E.projectiveCoordinate 2 ∈ E.projectiveGrading 1 := E.projectiveCoordinate_mem 2

/-- The structure morphism of the projective curve of `E`. -/
noncomputable example : E.ProjectiveScheme ⟶ Spec (CommRingCat.of ℚ) := E.projectiveSchemeToSpec

end ProjectiveSchemeTest
