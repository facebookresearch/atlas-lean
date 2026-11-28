/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeZeroSection
public import Mathlib.Algebra.Order.Field.Rat

/-! Tests for `MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeZeroSection`. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace ProjectiveSchemeZeroSectionTest

#check @WeierstrassCurve.irrelevant_le_span_coordinates
#check @WeierstrassCurve.iSup_basicOpen_projectiveCoordinate
#check @WeierstrassCurve.coordinate_zero_pow_three_mem_span
#check @WeierstrassCurve.mem_basicOpen_one_of_notMem_basicOpen_two
#check @WeierstrassCurve.chartAtInfinity_base_mem_basicOpen_two_iff
#check @WeierstrassCurve.ker_evalAtInfinity_le
#check @WeierstrassCurve.zAtInfinity_pow_three_mem_span
#check @WeierstrassCurve.eq_ker_evalAtInfinity
#check @WeierstrassCurve.specMap_evalAtInfinity_base_asIdeal
#check @WeierstrassCurve.range_zeroSection_eq_compl_basicOpen

/-- The curve `y² + y = x³ - x` over `ℚ`. -/
abbrev E : WeierstrassCurve ℚ := ⟨0, 0, 1, -1, 0⟩

/-- The point at infinity of `E` is the complement of the affine chart. -/
example : Set.range E.zeroSection.base =
    ((Proj.basicOpen E.projectiveGrading (E.projectiveCoordinate 2) :
      Set E.ProjectiveScheme))ᶜ :=
  E.range_zeroSection_eq_compl_basicOpen

/-- The cuspidal cubic `y² = x³` over `ℚ` (discriminant `0`) also has one point at infinity. -/
example : Set.range (⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve ℚ).zeroSection.base =
    ((Proj.basicOpen (⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve ℚ).projectiveGrading
      ((⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve ℚ).projectiveCoordinate 2) :
      Set (⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve ℚ).ProjectiveScheme))ᶜ :=
  WeierstrassCurve.range_zeroSection_eq_compl_basicOpen _

end ProjectiveSchemeZeroSectionTest
