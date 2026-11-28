/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeVariableChange

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace WeierstrassCurve

#check @projectiveSubst
#check @projectiveSubst_X_zero
#check @projectiveSubst_X_one
#check @projectiveSubst_X_two
#check @projectiveSubst_C
#check @projectiveSubst_polynomial
#check @projectiveSubst_inv_comp
#check @projectiveSubst_comp_inv
#check @projectiveSubst_isHomogeneous
#check @homogeneousVariableChangeAux
#check @homogeneousVariableChangeAux_mk
#check @homogeneousVariableChangeAux_comp
#check @homogeneousVariableChangeAux_comp'
#check @homogeneousVariableChangeAux_mem
#check @homogeneousVariableChangeEquiv
#check @projectiveGradedVariableChange
#check @projectiveGradedVariableChangeInv
#check @projectiveGradedVariableChange_comp_inv
#check @projectiveGradedVariableChangeInv_comp
#check @irrelevant_le_map_projectiveGradedVariableChange
#check @irrelevant_le_map_projectiveGradedVariableChangeInv
#check @projectiveSchemeVariableChangeIso
#check @projectiveSchemeVariableChangeIso_hom
#check @projectiveGradedVariableChange_mk
#check @projectiveGradedVariableChange_algebraMap
#check @zeroSection_comp_projectiveSchemeVariableChangeIso_hom
#check @projectiveSchemeVariableChangeIso_hom_projectiveSchemeToSpec
#check @affineVariableChange_eval
#check @affineVariableChange
#check @affineVariableChange_affineX
#check @affineVariableChange_affineY
#check @affineVariableChange_algebraMap
#check @affineChart_comp_projectiveSchemeVariableChangeIso_hom

/-- The curve `y² + y = x³ - x` over `ℤ` and the variable change `(u, r, s, t) = (-1, 1, 2, 3)`. -/
private abbrev testCurve : WeierstrassCurve ℤ := ⟨0, 0, 1, -1, 0⟩

private abbrev testChange : VariableChange ℤ := ⟨-1, 1, 2, 3⟩

/-- The homogeneous identity for the test curve over `ℤ`. -/
example : projectiveSubst testChange testCurve.toProjective.polynomial =
    MvPolynomial.C (((-1 : ℤˣ) : ℤ) ^ 6) * (testChange • testCurve).toProjective.polynomial :=
  projectiveSubst_polynomial testCurve testChange

/-- The graded isomorphism of homogeneous coordinate rings over `ℤ`. -/
noncomputable example :
    testCurve.HomogeneousCoordinateRing ≃ₐ[ℤ] (testChange • testCurve).HomogeneousCoordinateRing :=
  testCurve.homogeneousVariableChangeEquiv testChange

/-- The isomorphism of projective schemes over `ℤ`. -/
noncomputable example :
    (testChange • testCurve).ProjectiveScheme ≅ testCurve.ProjectiveScheme :=
  testCurve.projectiveSchemeVariableChangeIso testChange

/-- Over a field, the isomorphism preserves the zero section, lies over `Spec`, and restricts to
the affine variable change on the affine charts. -/
example (W : WeierstrassCurve ℚ) (C : VariableChange ℚ) :
    (C • W).zeroSection ≫ (W.projectiveSchemeVariableChangeIso C).hom = W.zeroSection ∧
      (W.projectiveSchemeVariableChangeIso C).hom ≫ W.projectiveSchemeToSpec =
        (C • W).projectiveSchemeToSpec ∧
      (C • W).affineChart ≫ (W.projectiveSchemeVariableChangeIso C).hom =
        Spec.map (CommRingCat.ofHom (W.affineVariableChange C)) ≫ W.affineChart :=
  ⟨W.zeroSection_comp_projectiveSchemeVariableChangeIso_hom C,
    W.projectiveSchemeVariableChangeIso_hom_projectiveSchemeToSpec C,
    W.affineChart_comp_projectiveSchemeVariableChangeIso_hom C⟩

/-- The inverse of the isomorphism is `Proj.map` of the map induced by `C⁻¹`, and the two
composites are identities. -/
example (W : WeierstrassCurve ℤ) (C : VariableChange ℤ) :
    (W.projectiveSchemeVariableChangeIso C).hom ≫ (W.projectiveSchemeVariableChangeIso C).inv =
      𝟙 _ :=
  (W.projectiveSchemeVariableChangeIso C).hom_inv_id

/-- The affine variable change on `x` for the test curve: `x ↦ (-1)² x' + 1`. -/
example : testCurve.affineVariableChange testChange testCurve.affineX =
    algebraMap ℤ _ (((-1 : ℤˣ) : ℤ) ^ 2) * (testChange • testCurve).affineX + algebraMap ℤ _ 1 :=
  testCurve.affineVariableChange_affineX testChange

end WeierstrassCurve
