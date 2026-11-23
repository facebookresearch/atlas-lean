/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationCommaNaturality

/-! # Tests for base naturality of second-coordinate comma translation -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.SInverseSSecondTranslationCommaNaturality

open CategoryTheory.SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check secondTranslationCostructuredMapNaturalityIso
#check secondTranslationCostructuredMapNaturalityIso_hom_app_left
#check secondTranslationCostructuredMapNaturalityObjEq
#check secondTranslationCostructuredMapNaturalityIso_hom_app_eqToHom
#check secondTranslationCostructuredMap_naturality
#check secondTranslationRightCommaNerveDiagramNatTrans
#check secondTranslationRightCommaNerveDiagramNatTrans_app
#check secondTranslationTranslatedRightCommaNerveDiagramNatTrans
#check secondTranslationTranslatedRightCommaNerveDiagramNatTrans_app

example (A : C) {B D : Translation C} (g : B ⟶ D) :
    CostructuredArrow.map g ⋙ secondTranslationCostructuredMap A D =
      secondTranslationCostructuredMap A B ⋙ CostructuredArrow.map g :=
  secondTranslationCostructuredMap_naturality A g

-- Identity base arrows use the same base-naturality theorem; no strict
-- identity claim about the resulting comma functors is needed.
example (A : C) (B : Translation C) :
    CostructuredArrow.map (𝟙 B) ⋙
        secondTranslationCostructuredMap A B =
      secondTranslationCostructuredMap A B ⋙
        CostructuredArrow.map (𝟙 B) :=
  secondTranslationCostructuredMap_naturality A (𝟙 B)

-- Translation by the zero object remains a functor equipped with the same
-- base naturality; it is not asserted to be definitionally the identity.
example {B D : Translation C} (g : B ⟶ D) :
    CostructuredArrow.map g ⋙
        secondTranslationCostructuredMap (0 : C) D =
      secondTranslationCostructuredMap (0 : C) B ⋙
        CostructuredArrow.map g :=
  secondTranslationCostructuredMap_naturality (0 : C) g

-- Boundary with the chosen zero base object.
example (A : C) :
    CostructuredArrow.map (𝟙 (⟨(0 : C)⟩ : Translation C)) ⋙
        secondTranslationCostructuredMap A (⟨(0 : C)⟩ : Translation C) =
      secondTranslationCostructuredMap A
          (⟨(0 : C)⟩ : Translation C) ⋙
        CostructuredArrow.map (𝟙 (⟨(0 : C)⟩ : Translation C)) :=
  secondTranslationCostructuredMap_naturality A
    (𝟙 (⟨(0 : C)⟩ : Translation C))

section SmallUniverse

variable {C₀ : Type} [Category.{0} C₀] [HasZeroMorphisms C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀]

example (A : C₀) :
    SSet.rightCommaNerveDiagram (translationProjection (C := C₀)) ⟶
      SSet.rightCommaNerveDiagram (translationProjection (C := C₀)) :=
  secondTranslationRightCommaNerveDiagramNatTrans A

example (A : C₀) :
    Translation.translateFunctor A ⋙
        SSet.rightCommaNerveDiagram (translationProjection (C := C₀)) ⟶
      Translation.translateFunctor A ⋙
        SSet.rightCommaNerveDiagram (translationProjection (C := C₀)) :=
  secondTranslationTranslatedRightCommaNerveDiagramNatTrans A

example (A : C₀) (B : Translation C₀) :
    (secondTranslationTranslatedRightCommaNerveDiagramNatTrans A).app B =
      nerveMap (secondTranslationCostructuredMap A
        ((Translation.translateFunctor A).obj B)) :=
  secondTranslationTranslatedRightCommaNerveDiagramNatTrans_app A B

end SmallUniverse

#print axioms secondTranslationCostructuredMapNaturalityIso
#print axioms secondTranslationCostructuredMap_naturality
#print axioms secondTranslationRightCommaNerveDiagramNatTrans
#print axioms secondTranslationTranslatedRightCommaNerveDiagramNatTrans

end MathlibExtTest.SInverseSSecondTranslationCommaNaturality

end
