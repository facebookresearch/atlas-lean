/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationBaseAction

/-!
# Diagonal translation over the additive S⁻¹S projection

Second-coordinate translation leaves the one-coordinate translation
projection unchanged.  Combining this with first-coordinate equivariance
shows that diagonal translation lies over left translation of the base.
Moreover, the natural arrow adding an object in both coordinates projects to
the canonical base-translation arrow.

These are the strict projection formulas needed before comparing translated
right-comma objects with cocartesian diagonal pushforward.  No comma
comparison, chain map, spectral-sequence map, localization, realization, or
CGWH claim is made here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Second-coordinate translation does not change the projected arrow. -/
@[simp]
theorem translationProjection_map_translateSecondFunctor_map
    (A : C) {X Y : Pair C} (f : X ⟶ Y) :
    translationProjection.map ((translateSecondFunctor A).map f) =
      translationProjection.map f := by
  induction f using Quotient.inductionOn
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Second-coordinate translation commutes with the projection by an
identity-component natural isomorphism. -/
noncomputable def translateSecondProjectionIso (A : C) :
    translateSecondFunctor A ⋙ translationProjection ≅
      translationProjection :=
  NatIso.ofComponents (fun X => Iso.refl _) (by
    intro X Y f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact translationProjection_map_translateSecondFunctor_map A f)

@[simp]
theorem translateSecondProjectionIso_hom_app (A : C) (X : Pair C) :
    (translateSecondProjectionIso A).hom.app X = 𝟙 _ :=
  rfl

/-- Second-coordinate translation lies strictly over the identity of the
one-coordinate base. -/
theorem translateSecondFunctor_comp_translationProjection (A : C) :
    translateSecondFunctor A ⋙ translationProjection =
      translationProjection :=
  Functor.ext_of_iso (translateSecondProjectionIso A)
    (fun _ => rfl) (fun _ => rfl)

/-- Add `A` in both coordinates, in the order used by the existing diagonal
addition natural transformation. -/
noncomputable abbrev diagonalTranslationFunctor (A : C) : Pair C ⥤ Pair C :=
  translateFirstFunctor A ⋙ translateSecondFunctor A

/-- Diagonal translation lies over left translation on the base. -/
noncomputable def diagonalTranslationProjectionIso (A : C) :
    diagonalTranslationFunctor A ⋙ translationProjection ≅
      translationProjection ⋙ Translation.translateFunctor A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (translateFirstFunctor A)
      (translateSecondProjectionIso A) ≪≫
    translateFirstProjectionIso A

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem diagonalTranslationProjectionIso_hom_app (A : C) (X : Pair C) :
    (diagonalTranslationProjectionIso A).hom.app X = 𝟙 _ := by
  simp only [diagonalTranslationProjectionIso, diagonalTranslationFunctor,
    Functor.comp_obj, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    translateSecondProjectionIso_hom_app,
    translateFirstProjectionIso_hom_app, Category.comp_id]

/-- Diagonal translation strictly covers left translation on the base. -/
theorem diagonalTranslationFunctor_comp_translationProjection (A : C) :
    diagonalTranslationFunctor A ⋙ translationProjection =
      translationProjection ⋙ Translation.translateFunctor A :=
  Functor.ext_of_iso (diagonalTranslationProjectionIso A)
    (fun _ => rfl) (diagonalTranslationProjectionIso_hom_app A)

/-- The total diagonal-addition arrow projects to the canonical
base-translation arrow. -/
@[simp]
theorem translationProjection_map_diagonalAddFirstSecondNatTrans_app
    (A : C) (X : Pair C) :
    translationProjection.map
        ((diagonalAddFirstSecondNatTrans A).app X) =
      (Translation.diagonalAddNatTrans A).app
        (translationProjection.obj X) :=
  rfl

end SInverseS
end CategoryTheory

end
