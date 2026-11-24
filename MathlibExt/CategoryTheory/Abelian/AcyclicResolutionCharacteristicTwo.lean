/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.DerivedKilledBy
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ComputedAcyclicNormalization
public import MathlibExt.CategoryTheory.Abelian.RightDerived.SignedBoundaryCompatibility

/-!
# The original acyclic comparisons on two-torsion coefficients

Only the coefficient object is assumed killed by two. The original target category may contain
arbitrary abelian groups. The retained acyclic, computed augmented-resolution and injective maps
remain unchanged.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace CategoryTheory.Preadditive
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The proved triangular normalization acts trivially from an two-torsion object. -/
theorem IsKilledBy.normalization_sign_hom_source {A B : C} (hA : IsKilledBy A 2)
    (f : A ⟶ B) (n : ℕ) :
    ProjectiveResolution.acyclicResolutionNormalizationSign n • f = f := by
  rw [ProjectiveResolution.acyclicResolutionNormalizationSign_closed]
  exact hA.neg_one_pow_zsmul_hom_source f _

/-- The proved triangular normalization acts trivially into an two-torsion object. -/
theorem IsKilledBy.normalization_sign_hom_target {A B : C} (hB : IsKilledBy B 2)
    (f : A ⟶ B) (n : ℕ) :
    ProjectiveResolution.acyclicResolutionNormalizationSign n • f = f := by
  rw [ProjectiveResolution.acyclicResolutionNormalizationSign_closed]
  exact hB.neg_one_pow_zsmul_hom_target f _

/-- The normalization iso is the identity on the given two-torsion object. -/
theorem IsKilledBy.normalization_iso_eq_refl {A : C} (hA : IsKilledBy A 2) (n : ℕ) :
    ProjectiveResolution.acyclicResolutionNormalizationIso A n = Iso.refl A := by
  apply Iso.ext
  exact hA.normalization_sign_hom_source (𝟙 A) n

end CategoryTheory.Preadditive

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive]

/-- Every original right-derived normalization component is the identity in all degrees. -/
theorem rightDerived_normalizationIso_app_eq_refl {X : C} (hX : IsKilledBy X 2) (n : ℕ) :
    ((F.rightDerived n).acyclicResolutionNormalizationIso n).app X =
      Iso.refl ((F.rightDerived n).obj X) :=
  (F.rightDerived_obj_isKilledBy hX n).normalization_iso_eq_refl n

set_option backward.isDefEq.respectTransparency false in
/-- For two-torsion coefficients the corrected and retained acyclic isos coincide. -/
theorem rightDerivedNormalizedAcyclicComparison_eq_retained [PreservesFiniteLimits F]
    {X : C} (hX : IsKilledBy X 2)
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q))) (n : ℕ) :
    F.rightDerivedNormalizedAcyclicComparison I ι hI n =
      F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n := by
  apply Iso.ext
  change (ProjectiveResolution.acyclicResolutionNormalizationSign n •
      𝟙 ((F.rightDerived n).obj X)) ≫
      (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n).hom = _
  rw [zsmul_comp, Category.id_comp]
  exact (F.rightDerived_obj_isKilledBy hX n).normalization_sign_hom_source _ n

set_option backward.isDefEq.respectTransparency false in
/-- The SAME retained comparison has the unsigned square for every augmented map. -/
theorem rightDerivedAcyclicComparison_toInjective_of_twoTorsion [PreservesFiniteLimits F]
    {X Y : C} (hX : IsKilledBy X 2)
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q)))
    (J : InjectiveResolution Y) (f : X ⟶ Y) (a : I ⟶ J.cocomplex)
    (h : ι ≫ a = (CochainComplex.single₀ C).map f ≫ J.ι) (n : ℕ) :
    (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n).hom ≫
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map a) n =
    (F.rightDerived n).map f ≫ (J.isoRightDerivedObj F n).hom := by
  have hs := F.rightDerivedAcyclicComparison_toInjective_signed I ι hI J f a h n
  exact hs.trans ((F.rightDerived_obj_isKilledBy hX n).normalization_sign_hom_source _ n)

set_option backward.isDefEq.respectTransparency false in
/-- On the SAME injective resolution the retained acyclic iso is exactly the iso. -/
theorem rightDerivedAcyclicComparison_injective_of_twoTorsion [PreservesFiniteLimits F]
    {X : C} (hX : IsKilledBy X 2) (J : InjectiveResolution X)
    (hJ : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (J.cocomplex.X q))) (n : ℕ) :
    F.rightDerivedObjIsoHomologyOfAcyclicResolution J.cocomplex J.ι hJ n =
      J.isoRightDerivedObj F n := by
  rw [← F.rightDerivedNormalizedAcyclicComparison_eq_retained hX]
  exact F.rightDerivedNormalizedAcyclicComparison_injective J hJ n

set_option backward.isDefEq.respectTransparency false in
/-- The SAME computed augmented-resolution map is the unsigned inverse of the retained iso. -/
theorem augmentedResolutionToRightDerivedHom_eq_retained_inv_of_twoTorsion
    [PreservesFiniteLimits F] {X : C} (hX : IsKilledBy X 2)
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q))) (n : ℕ) :
    F.augmentedResolutionToRightDerivedHom I ι n =
      (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n).inv := by
  rw [F.augmentedResolutionToRightDerivedHom_eq_signed_retained_inv I ι hI n]
  exact (F.rightDerived_obj_isKilledBy hX n).normalization_sign_hom_target _ n

set_option backward.isDefEq.respectTransparency false in
/-- The retained and computed maps compose to the identity on two-torsion derivation. -/
theorem augmentedResolutionToRightDerivedHom_retained_composition_of_twoTorsion
    [PreservesFiniteLimits F] {X : C} (hX : IsKilledBy X 2)
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q))) (n : ℕ) :
    (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n).hom ≫
      F.augmentedResolutionToRightDerivedHom I ι n =
      𝟙 ((F.rightDerived n).obj X) := by
  rw [F.augmentedResolutionToRightDerivedHom_eq_retained_inv_of_twoTorsion hX I ι hI n]
  exact Iso.hom_inv_id _

set_option backward.isDefEq.respectTransparency false in
/-- Retained resolution homology inherits the original coefficient's torsion. -/
theorem rightDerivedAcyclicHomology_isKilledBy [PreservesFiniteLimits F]
    {X : C} {m : ℕ} (hX : IsKilledBy X m)
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q))) (n : ℕ) :
    IsKilledBy (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I).homology n) m :=
  (F.rightDerived_obj_isKilledBy hX n).of_iso
    (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n)

/-- Every adjacent-degree sign acts trivially on the coefficient connector. -/
theorem rightDerivedConnecting_sign_of_twoTorsion
    (S : ShortComplex.ShortExactSequences C) (hS : IsKilledBy S.obj.X₃ 2) (n : ℕ) :
    ((-1 : ℤ) ^ (n + 1)) • (F.rightDerivedConnecting n).app S =
      (F.rightDerivedConnecting n).app S :=
  (F.rightDerived_obj_isKilledBy hS n).neg_one_pow_zsmul_hom_source _ (n + 1)

set_option backward.isDefEq.respectTransparency false in
/-- The SAME coefficient connector is unchanged by source and target normalization. -/
theorem rightDerivedConnecting_normalization_conjugate_of_twoTorsion
    (S : ShortComplex.ShortExactSequences C) (hS : IsKilledBy S.obj.X₃ 2) (n : ℕ) :
    ((F.rightDerived n).acyclicResolutionNormalizationIso n).hom.app S.obj.X₃ ≫
      (F.rightDerivedConnecting n).app S ≫
      ((F.rightDerived (n + 1)).acyclicResolutionNormalizationIso (n + 1)).inv.app S.obj.X₁ =
      (F.rightDerivedConnecting n).app S := by
  rw [F.rightDerivedConnecting_normalization_conjugate_closed]
  exact F.rightDerivedConnecting_sign_of_twoTorsion S hS n

end CategoryTheory.Functor
