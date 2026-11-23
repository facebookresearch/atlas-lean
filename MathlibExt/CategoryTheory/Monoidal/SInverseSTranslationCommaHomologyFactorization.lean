/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.Basic
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationComma
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Homology factorization of translation-category base change

The canonical base-change map on a right-comma category is simplicially
homotopic to diagonal translation.  Diagonal translation, in turn, is
naturally isomorphic to first-coordinate translation followed by fiberwise
second-coordinate translation.  Homotopy and natural-isomorphism invariance
therefore factor the base-change map on right-comma homology through these two
translation maps.

No strict-fiber identification, localization, spectral-sequence edge map,
realization, or CGWH statement is made here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Base postcomposition and diagonal translation induce the same map on
right-comma homology. -/
theorem baseChange_homologyMap_eq_diagonalTranslation
    (R : AddCommGrpCat.{u}) (A : C) (B : Translation C) (n : ℕ) :
    SSet.homologyMap
        (nerveMap (CostructuredArrow.map
          ((Translation.diagonalAddNatTrans A).app B))) R n =
      SSet.homologyMap
        (nerveMap (diagonalTranslationCostructuredMap A B)) R n :=
  (baseChangeToDiagonalTranslationNerveHomotopy A B).congr_homologyMap R n

/-- First-then-second comma translation and diagonal comma translation
induce the same map on homology. -/
theorem firstSecond_homologyMap_eq_diagonalTranslation
    (R : AddCommGrpCat.{u}) (A : C) (B : Translation C) (n : ℕ) :
    SSet.homologyMap
        (nerveMap
          (translationCostructuredMap A B ⋙
            secondTranslationCostructuredMap A
              ((Translation.translateFunctor A).obj B))) R n =
      SSet.homologyMap
        (nerveMap (diagonalTranslationCostructuredMap A B)) R n := by
  exact (NatTrans.nerveHomotopy
    (firstSecondTranslationCostructuredIso A B).hom).congr_homologyMap R n

/-- On right-comma homology, base change along the canonical translation
arrow is first-coordinate translation followed by fiberwise
second-coordinate translation. -/
theorem baseChange_homologyMap_eq_first_comp_second
    (R : AddCommGrpCat.{u}) (A : C) (B : Translation C) (n : ℕ) :
    SSet.homologyMap
        (nerveMap (CostructuredArrow.map
          ((Translation.diagonalAddNatTrans A).app B))) R n =
      SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R n ≫
        SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap A
            ((Translation.translateFunctor A).obj B))) R n := by
  rw [← SSet.homologyMap_comp]
  rw [nerveMap_comp]
  exact (baseChange_homologyMap_eq_diagonalTranslation C R A B n).trans
    (firstSecond_homologyMap_eq_diagonalTranslation C R A B n).symm

end SInverseS
end CategoryTheory

end
