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
chart. -/
example : (E.projectiveSchemeVariableChangeIso C).hom =
    (E.projectiveSchemeVariableChangeIso C).hom :=
  E.eq_projectiveSchemeVariableChangeIso_hom C _
    (E.projectiveSchemeVariableChangeIso_hom_projectiveSchemeToSpec C)
    (E.affineChart_comp_projectiveSchemeVariableChangeIso_hom C)

end ProjectiveSchemeIsoVariableChangeTest
