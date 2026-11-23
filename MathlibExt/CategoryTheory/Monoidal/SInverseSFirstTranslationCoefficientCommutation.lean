/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSFirstSecondTranslationCommaInterchange
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationCoefficient

/-!
# Monomial commutation for conjugated first-coordinate translation

Conjugating first-coordinate right-comma homology translation through the
comma/core coefficient comparison gives an endomorphism of the underlying
core coefficient group.  Arbitrary first/second translation interchange and
the second-translation coefficient square show that this endomorphism
commutes with every skeleton monomial.

Only comparison-isomorphism components are cancelled.  This file does not
cancel a monomial map, package a linear morphism, or perform localization.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- First-coordinate right-comma homology translation, conjugated to an
endomorphism of the underlying core translation coefficient group. -/
noncomputable def conjugatedFirstTranslationCoefficientMap
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).obj
        (coreTranslationHomologyModuleCat C R q) ⟶
      (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).obj
        (coreTranslationHomologyModuleCat C R q) :=
  (costructuredCoreTranslationCoefficientNatIso C R q).inv.app B ≫
    SSet.homologyMap
      (nerveMap (translationCostructuredMap A B)) R q ≫
    (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
      ((Translation.translateFunctor A).obj B)

/-- The conjugated first-coordinate translation map commutes with every
skeleton-monomial action on the core coefficient group. -/
theorem conjugatedFirstTranslationCoefficientMap_comm_monomial
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C)
    (x : Skeleton C) :
    conjugatedFirstTranslationCoefficientMap C R q A B ≫
        (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
          (coreTranslationCoefficientMap C R q x) =
      (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
          (coreTranslationCoefficientMap C R q x) ≫
        conjugatedFirstTranslationCoefficientMap C R q A B := by
  let T := (Translation.translateFunctor A).obj B
  let κ := costructuredCoreTranslationCoefficientNatIso C R q
  let F := SSet.homologyMap
    (nerveMap (translationCostructuredMap A B)) R q
  let S_B := SSet.homologyMap
    (nerveMap (secondTranslationCostructuredMap x.out B)) R q
  let S_T := SSet.homologyMap
    (nerveMap (secondTranslationCostructuredMap x.out T)) R q
  let m := (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
    (coreTranslationCoefficientMap C R q x)
  have hx : toSkeleton x.out = x := toSkeleton_fromSkeleton_obj x
  have hSecondB : S_B ≫ κ.hom.app B = κ.hom.app B ≫ m := by
    simpa only [S_B, κ, m, hx] using
      secondTranslationCostructured_homologyMap_comp_coreCoefficientComparison
        C R x.out B q
  have hSecondT : S_T ≫ κ.hom.app T = κ.hom.app T ≫ m := by
    simpa only [S_T, κ, m, hx] using
      secondTranslationCostructured_homologyMap_comp_coreCoefficientComparison
        C R x.out T q
  have hInterchange : F ≫ S_T = S_B ≫ F := by
    exact firstSecondTranslationCostructured_homologyMap_comm
      C R q A x.out B
  have hInv : κ.inv.app B ≫ S_B = m ≫ κ.inv.app B := by
    apply (cancel_mono (κ.hom.app B)).1
    calc
      (κ.inv.app B ≫ S_B) ≫ κ.hom.app B =
          κ.inv.app B ≫ (S_B ≫ κ.hom.app B) :=
        Category.assoc _ _ _
      _ = κ.inv.app B ≫ (κ.hom.app B ≫ m) := by
        rw [hSecondB]
      _ = m := by simp
      _ = (m ≫ κ.inv.app B) ≫ κ.hom.app B := by
        simp only [Category.assoc, Iso.inv_hom_id_app]
        exact (Category.comp_id m).symm
  change (κ.inv.app B ≫ F ≫ κ.hom.app T) ≫ m =
    m ≫ (κ.inv.app B ≫ F ≫ κ.hom.app T)
  calc
    (κ.inv.app B ≫ F ≫ κ.hom.app T) ≫ m =
        κ.inv.app B ≫ F ≫ (κ.hom.app T ≫ m) := by
      simp only [Category.assoc]
    _ = κ.inv.app B ≫ F ≫ (S_T ≫ κ.hom.app T) := by
      rw [← hSecondT]
    _ = κ.inv.app B ≫ (F ≫ S_T) ≫ κ.hom.app T := by
      simp only [Category.assoc]
    _ = κ.inv.app B ≫ (S_B ≫ F) ≫ κ.hom.app T := by
      rw [hInterchange]
    _ = (κ.inv.app B ≫ S_B) ≫ F ≫ κ.hom.app T := by
      simp only [Category.assoc]
    _ = (m ≫ κ.inv.app B) ≫ F ≫ κ.hom.app T := by
      rw [hInv]
    _ = m ≫ (κ.inv.app B ≫ F ≫ κ.hom.app T) := by
      simp only [Category.assoc]

end SInverseS
end CategoryTheory

end
