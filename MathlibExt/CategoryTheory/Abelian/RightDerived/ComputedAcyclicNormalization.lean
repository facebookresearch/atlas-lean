/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.SignedAugmentedAcyclicResolutionComparison
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AugmentedResolutionComparison

/-!
## # The SAME computed augmented-resolution map and the retained triangular normalization
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

set_option backward.isDefEq.respectTransparency false in
/--
The chosen augmented comparison composed with the SAME retained acyclic iso has exactly the proved
triangular scalar in every degree.
-/
theorem augmentedResolutionToRightDerivedHom_retained_composition (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] {X : C}
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q))) (n : ℕ) :
    (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n).hom ≫
      F.augmentedResolutionToRightDerivedHom I ι n =
    ProjectiveResolution.acyclicResolutionNormalizationSign n • 𝟙 ((F.rightDerived n).obj X) := by
  let J := injectiveResolution X
  let a := augmentedResolutionComparison I ι
  let E := F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n
  let p : (F.rightDerived n).obj X ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).homology n :=
    J.isoRightDerivedObj F n
  let m : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I).homology n ⟶
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).homology n :=
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map a.val) n
  have ha : ι ≫ a.val = (CochainComplex.single₀ C).map (𝟙 X) ≫ J.ι := by
    rw [Functor.map_id, Category.id_comp]
    exact a.property
  have hs := F.rightDerivedAcyclicComparison_toInjective_signed I ι hI J (𝟙 X) a.val ha n
  have hm : E.hom ≫ m = ProjectiveResolution.acyclicResolutionNormalizationSign n • p.hom := by
    simpa only [Functor.map_id, Category.id_comp] using hs
  change E.hom ≫ (m ≫ p.inv) =
    ProjectiveResolution.acyclicResolutionNormalizationSign n • 𝟙 ((F.rightDerived n).obj X)
  rw [← Category.assoc, hm, zsmul_comp, p.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in
/--
The SAME computed map from resolution homology to derivation is the proved triangular scalar times
the inverse of the SAME retained acyclic comparison.
-/
theorem augmentedResolutionToRightDerivedHom_eq_signed_retained_inv (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] {X : C}
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q))) (n : ℕ) :
    F.augmentedResolutionToRightDerivedHom I ι n =
    ProjectiveResolution.acyclicResolutionNormalizationSign n •
      (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n).inv := by
  let E := F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n
  have h := F.augmentedResolutionToRightDerivedHom_retained_composition I ι hI n
  have he := congrArg (fun t => E.inv ≫ t) h
  change E.inv ≫ (E.hom ≫ F.augmentedResolutionToRightDerivedHom I ι n) =
    E.inv ≫ (ProjectiveResolution.acyclicResolutionNormalizationSign n •
      𝟙 ((F.rightDerived n).obj X)) at he
  simpa only [Iso.inv_hom_id_assoc, comp_zsmul, Category.comp_id] using he

set_option backward.isDefEq.respectTransparency false in
/-- The complete corrected retained iso has exactly the SAME computed original
augmented-resolution-to-derived morphism as its inverse. -/
theorem augmentedResolutionToRightDerivedHom_eq_normalized_inv (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] {X : C}
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q))) (n : ℕ) :
    F.augmentedResolutionToRightDerivedHom I ι n =
      (F.rightDerivedNormalizedAcyclicComparison I ι hI n).inv := by
  rw [F.augmentedResolutionToRightDerivedHom_eq_signed_retained_inv I ι hI n]
  change ProjectiveResolution.acyclicResolutionNormalizationSign n •
      (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n).inv =
    (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n).inv ≫
      (ProjectiveResolution.acyclicResolutionNormalizationSign n •
        𝟙 ((F.rightDerived n).obj X))
  rw [comp_zsmul, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
The computed augmented-resolution comparison is an isomorphism for the termwise acyclic
resolution, with no injectivity assumption on its own terms.
-/
theorem isIso_augmentedResolutionToRightDerivedHom_of_acyclic (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] {X : C}
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q))) (n : ℕ) :
    IsIso (F.augmentedResolutionToRightDerivedHom I ι n) := by
  rw [F.augmentedResolutionToRightDerivedHom_eq_normalized_inv I ι hI n]
  infer_instance

end CategoryTheory.Functor
