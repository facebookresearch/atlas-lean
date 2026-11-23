/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CoherentAnalyticHypercohomology

@[expose] public section

/-!
# Tests for the coherent analytic hypercohomology comparison

The analytic module pullback is a left adjoint and preserves finite colimits.
Given its exactness, it is additive, and the hypercohomology comparison is
additive and sends zero to zero; it is the derived pullback of a class,
composed with the unit and shift identifications.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.AnalyticRealization
open MathlibExt.AlgebraicGeometry.CoherentAnalyticHypercohomology

namespace MathlibExtTest.AlgebraicGeometry.CoherentAnalyticHypercohomology

attribute [local instance] HasDerivedCategory.standard

variable (X : ComplexScheme) (d : ℕ) [AnalyticManifold X d] [RegularFunctions X d]

example : (pullback X d).IsLeftAdjoint := inferInstance

example : PreservesFiniteColimits (pullback X d) := inferInstance

variable [PreservesFiniteLimits (pullback X d)]

example : (pullback X d).Additive := inferInstance

example (K : CochainComplex X.left.Modules ℤ) (n : ℤ) :
    comparison X d K n 0 = 0 := by
  simp [comparison]

example (K : CochainComplex X.left.Modules ℤ) (n : ℤ)
    (a b : AlgebraicHypercohomology X K n) :
    comparison X d K n (a + b) = comparison X d K n a + comparison X d K n b :=
  comparison_add X d K n a b

example (K : CochainComplex X.left.Modules ℤ) (n : ℤ)
    (a : AlgebraicHypercohomology X K n) :
    comparison X d K n a = (derivedUnitIso X d).inv ≫ (derivedPullback X d).map a ≫
      ((derivedPullback X d).commShiftIso n).hom.app (DerivedCategory.Q.obj K) :=
  rfl

end MathlibExtTest.AlgebraicGeometry.CoherentAnalyticHypercohomology
