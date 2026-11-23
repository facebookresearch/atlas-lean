/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSCostructuredCoefficientComparison
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationDiagonalStabilizer

/-!
# Canonical base change on right-comma homology coefficients

Under the natural right-comma/core-module coefficient comparison, base change
along the canonical arrow `B ⟶ A ⊞ B` is scalar multiplication by the
skeleton monomial `[A]`.

This file makes no localization or cancellation claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Canonical base change on right-comma homology is conjugate to the
underlying core-coefficient monomial map for `[A]`. -/
theorem diagonalAdd_homologyMap_comp_coreCoefficientComparison
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    SSet.homologyMap
          (nerveMap (CostructuredArrow.map
            ((Translation.diagonalAddNatTrans A).app B))) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj B) =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
          (coreTranslationCoefficientMap C R q (toSkeleton A)) := by
  have h :=
    (costructuredCoreTranslationCoefficientNatIso C R q).hom.naturality
      ((Translation.diagonalAddNatTrans A).app B)
  change SSet.homologyMap
        (nerveMap (CostructuredArrow.map
          ((Translation.diagonalAddNatTrans A).app B))) R q ≫
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
        ((Translation.translateFunctor A).obj B) =
    (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
      (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
        ((coreTranslationCoefficientFunctor C R q).map
          ((Translation.diagonalAddNatTrans A).app B)) at h
  rw [coreTranslationCoefficientFunctor_map_diagonalAdd] at h
  exact h

end SInverseS
end CategoryTheory

end
