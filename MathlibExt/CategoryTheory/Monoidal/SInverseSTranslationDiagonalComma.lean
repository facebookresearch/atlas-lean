/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationCommaAction
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationDiagonalProjection

/-!
# Diagonal translation on additive S⁻¹S right-comma categories

The projection square for diagonal translation induces a right-comma functor
via `CostructuredArrow.map₂`.  Postcomposition along the canonical base
translation arrow maps naturally to this diagonal functor: the left component
is the total diagonal-addition arrow.  Its comma equation is precisely the
projected diagonal-addition formula followed by naturality of the base
translation arrow.  Applying the existing nerve-homotopy API packages this
comparison simplicially.

This file does not yet pass to strict fibers, chains, spectral sequences,
localization, realization, or CGWH.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Diagonal translation induces a functor on right-comma categories. -/
noncomputable def diagonalTranslationCostructuredMap
    (A : C) (B : Translation C) :
    CostructuredArrow (translationProjection (C := C)) B ⥤
      CostructuredArrow (translationProjection (C := C))
        ((Translation.translateFunctor A).obj B) :=
  CostructuredArrow.map₂
    (diagonalTranslationProjectionIso A).hom
    (𝟙 ((Translation.translateFunctor A).obj B))

@[simp]
theorem diagonalTranslationCostructuredMap_obj_left
    (A : C) (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    ((diagonalTranslationCostructuredMap A B).obj X).left =
      (diagonalTranslationFunctor A).obj X.left :=
  rfl

@[simp]
theorem diagonalTranslationCostructuredMap_obj_hom
    (A : C) (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    ((diagonalTranslationCostructuredMap A B).obj X).hom =
      (diagonalTranslationProjectionIso A).hom.app X.left ≫
        (Translation.translateFunctor A).map X.hom ≫
        𝟙 ((Translation.translateFunctor A).obj B) :=
  CostructuredArrow.map₂_obj_hom _ _ _

@[simp]
theorem diagonalTranslationCostructuredMap_map_left
    (A : C) (B : Translation C)
    {X Y : CostructuredArrow (translationProjection (C := C)) B}
    (f : X ⟶ Y) :
    ((diagonalTranslationCostructuredMap A B).map f).left =
      (diagonalTranslationFunctor A).map f.left :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Postcomposition along the canonical base-translation arrow maps
naturally to diagonal translation of the total comma object. -/
noncomputable def baseChangeToDiagonalTranslationNatTrans
    (A : C) (B : Translation C) :
    CostructuredArrow.map ((Translation.diagonalAddNatTrans A).app B) ⟶
      diagonalTranslationCostructuredMap A B where
  app X := CostructuredArrow.homMk
    ((diagonalAddFirstSecondNatTrans A).app X.left) (by
      simpa [diagonalTranslationCostructuredMap, Category.assoc] using
        ((Translation.diagonalAddNatTrans A).naturality X.hom).symm)
  naturality {X Y} f := by
    apply CostructuredArrow.ext
    simpa [diagonalTranslationCostructuredMap] using
      (diagonalAddFirstSecondNatTrans A).naturality f.left

@[simp]
theorem baseChangeToDiagonalTranslationNatTrans_app_left
    (A : C) (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    ((baseChangeToDiagonalTranslationNatTrans A B).app X).left =
      (diagonalAddFirstSecondNatTrans A).app X.left :=
  by
    dsimp only [baseChangeToDiagonalTranslationNatTrans]
    rfl

/-- The two right-comma nerve maps are simplicially homotopic. -/
noncomputable def baseChangeToDiagonalTranslationNerveHomotopy
    (A : C) (B : Translation C) :
    SSet.Homotopy
      (nerveMap
        (CostructuredArrow.map
          ((Translation.diagonalAddNatTrans A).app B)))
      (nerveMap (diagonalTranslationCostructuredMap A B)) :=
  NatTrans.nerveHomotopy (baseChangeToDiagonalTranslationNatTrans A B)

end SInverseS
end CategoryTheory

end
