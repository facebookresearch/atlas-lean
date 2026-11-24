/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.AcyclicResolutionCharacteristicTwo
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.AcyclicResolutionSignedCorrection

/-!
# The SAME original projective acyclic comparison on two-torsion coefficients
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

/-- The original left-derived scalar component is the identity on two-torsion coefficients. -/
theorem leftDerived_normalizationIso_app_eq_refl (F : C ⥤ D) [F.Additive]
    {X : C} (hX : IsKilledBy X 2) (n : ℕ) :
    ((F.leftDerived n).acyclicResolutionNormalizationIso n).app X =
      Iso.refl ((F.leftDerived n).obj X) :=
  (F.leftDerived_obj_isKilledBy hX n).normalization_iso_eq_refl n

set_option backward.isDefEq.respectTransparency false in
/-- The SAME retained projective comparison is in every degree on two-torsion coefficients. -/
theorem leftDerivedAcyclicComparison_of_twoTorsion (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F] {X : C} (hX : IsKilledBy X 2)
    (P : ProjectiveResolution X) (n : ℕ) :
    F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π
        (normalizationProjectiveTerms_acyclic P F) n = P.isoLeftDerivedObj F n := by
  apply Iso.ext
  rw [normalizationAcyclicProjective_hom]
  exact (F.leftDerived_obj_isKilledBy hX n).normalization_sign_hom_source _ n

end CategoryTheory.ProjectiveResolution
