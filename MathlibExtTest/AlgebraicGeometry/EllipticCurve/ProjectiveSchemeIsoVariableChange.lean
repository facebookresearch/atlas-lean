/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeIsoVariableChange
public import Mathlib.Algebra.Order.Field.Rat

/-! Tests for `MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeIsoVariableChange`. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace ProjectiveSchemeIsoVariableChangeTest

#check @WeierstrassCurve.eq_projectiveSchemeVariableChangeIso_hom
#check @WeierstrassCurve.eq_projectiveSchemeVariableChangeIso_hom_of_affineChartAlgEquiv

/-- The curve `y² + y = x³ - x` over `ℚ`. -/
abbrev E : WeierstrassCurve ℚ := ⟨0, 0, 1, -1, 0⟩

/-- The variable change `(u, r, s, t) = (-1, 1, 2, 3)` over `ℚ`. -/
abbrev C : WeierstrassCurve.VariableChange ℚ := ⟨-1, 1, 2, 3⟩

example : IsDominant E.affineChart := inferInstance

/-- The isomorphism of the variable change is characterized by its restriction to the affine
chart: any morphism over `ℚ` that is the affine variable change on the chart is that isomorphism. -/
example (φ : (C • E).ProjectiveScheme ⟶ E.ProjectiveScheme)
    (h₁ : φ ≫ E.projectiveSchemeToSpec = (C • E).projectiveSchemeToSpec)
    (h₂ : (C • E).affineChart ≫ φ =
      Spec.map (CommRingCat.ofHom (E.affineVariableChange C)) ≫ E.affineChart) :
    φ = (E.projectiveSchemeVariableChangeIso C).hom :=
  E.eq_projectiveSchemeVariableChangeIso_hom C φ h₁ h₂

end ProjectiveSchemeIsoVariableChangeTest
