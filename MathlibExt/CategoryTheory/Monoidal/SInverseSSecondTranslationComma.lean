/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationDiagonalComma

/-!
# Second-coordinate translation on additive S⁻¹S right-comma categories

Because second-coordinate translation leaves the one-coordinate base fixed,
it induces an endofunctor of each right-comma category.  Composing the
first-coordinate translated comma functor with this fiberwise endofunctor is
canonically isomorphic to diagonal translation.

This is a categorical factorization only.  It makes no homology,
localization, spectral-sequence, realization, or CGWH claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Projection comparison in the exact unital shape expected by
`CostructuredArrow.map₂`. -/
noncomputable def secondTranslationProjectionNatTrans (A : C) :
    translateSecondFunctor A ⋙ translationProjection ⟶
      translationProjection ⋙ Functor.id (Translation C) :=
  (translateSecondProjectionIso A).hom ≫
    (Functor.rightUnitor translationProjection).inv

@[simp]
theorem secondTranslationProjectionNatTrans_app (A : C) (X : Pair C) :
    (secondTranslationProjectionNatTrans A).app X = 𝟙 _ := by
  simp [secondTranslationProjectionNatTrans, translateSecondFunctor]

/-- Second-coordinate translation induces an endofunctor on every
right-comma category of the translation projection. -/
noncomputable def secondTranslationCostructuredMap
    (A : C) (B : Translation C) :
    CostructuredArrow (translationProjection (C := C)) B ⥤
      CostructuredArrow (translationProjection (C := C)) B :=
  CostructuredArrow.map₂
    (U := translationProjection (C := C))
    (F := translateSecondFunctor A)
    (G := Functor.id (Translation C))
    (secondTranslationProjectionNatTrans A) (𝟙 B)

@[simp]
theorem secondTranslationCostructuredMap_obj_left
    (A : C) (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    ((secondTranslationCostructuredMap A B).obj X).left =
      (translateSecondFunctor A).obj X.left :=
  rfl

@[simp]
theorem secondTranslationCostructuredMap_obj_hom
    (A : C) (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    ((secondTranslationCostructuredMap A B).obj X).hom =
      (secondTranslationProjectionNatTrans A).app X.left ≫
        (Functor.id (Translation C)).map X.hom ≫ 𝟙 B :=
  CostructuredArrow.map₂_obj_hom _ _ _

@[simp]
theorem secondTranslationCostructuredMap_map_left
    (A : C) (B : Translation C)
    {X Y : CostructuredArrow (translationProjection (C := C)) B}
    (f : X ⟶ Y) :
    ((secondTranslationCostructuredMap A B).map f).left =
      (translateSecondFunctor A).map f.left :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- First-coordinate comma translation followed by fiberwise
second-coordinate translation is diagonal comma translation. -/
noncomputable def firstSecondTranslationCostructuredIso
    (A : C) (B : Translation C) :
    translationCostructuredMap A B ⋙
        secondTranslationCostructuredMap A
          ((Translation.translateFunctor A).obj B) ≅
      diagonalTranslationCostructuredMap A B :=
  NatIso.ofComponents
    (fun X => CostructuredArrow.isoMk (Iso.refl _) (by
      simp [translationCostructuredMap,
        secondTranslationCostructuredMap,
        secondTranslationProjectionNatTrans,
        diagonalTranslationCostructuredMap,
        diagonalTranslationProjectionIso]))
    (by
      intro X Y f
      apply CostructuredArrow.ext
      simp [translationCostructuredMap,
        secondTranslationCostructuredMap,
        secondTranslationProjectionNatTrans,
        diagonalTranslationCostructuredMap])

@[simp]
theorem firstSecondTranslationCostructuredIso_hom_app_left
    (A : C) (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    ((firstSecondTranslationCostructuredIso A B).hom.app X).left = 𝟙 _ := by
  change (Iso.refl _).hom = 𝟙 _
  rfl

end SInverseS
end CategoryTheory

end
