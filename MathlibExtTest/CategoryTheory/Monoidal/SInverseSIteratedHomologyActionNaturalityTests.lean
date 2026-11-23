/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import Mathlib.Data.ZMod.Basic
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSIteratedHomologyActionNaturality

/-! # Tests for iterated BK/core-coefficient action naturality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace MathlibExtTest.SInverseSIteratedHomologyActionNaturality

local instance (A : Type) [Ring A] : HasCoproducts.{0} (ModuleCat.{0} A) := by
  let h : HasColimitsOfSize.{0, 0} (ModuleCat.{0} A) := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

open CategoryTheory.SInverseS

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

local notation "U" =>
  forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat
local notation "c" => ComplexShape.down ℕ

#check translatedCostructuredCoreTranslationCoefficientNatIso
#check translatedCostructuredCoreTranslationCoefficientNatIso_hom_naturality
#check homologyWithCoefficientsForgetIso_inv_naturality
#check translationBKIteratedHomologyCoefficientIso
#check translatedTranslationBKIteratedHomologyCoefficientIso
#check translationBKIteratedHomologyCoefficientIso_hom_naturality

-- The translated coefficient comparison retains both explicit
-- reassociations; in particular its target is `(T ⋙ M) ⋙ U`.
example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) :
    translatedCostructuredCoreTranslationCoefficientNatIso C R q A =
      Functor.associator
          (Translation.translateFunctor A)
          (SSet.rightCommaNerveDiagram (translationProjection (C := C)))
          (SSet.homologyFunctor R q) ≪≫
        Functor.isoWhiskerLeft (Translation.translateFunctor A)
          (costructuredCoreTranslationCoefficientNatIso C R q) ≪≫
        (Functor.associator
          (Translation.translateFunctor A)
          (coreTranslationCoefficientFunctor C R q) U).symm :=
  rfl

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) :
    Functor.whiskerRight
          (translationRightCommaNerveDiagramNatTrans A)
          (SSet.homologyFunctor R q) ≫
        (translatedCostructuredCoreTranslationCoefficientNatIso
          C R q A).hom =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom ≫
        Functor.whiskerRight
          (conjugatedFirstTranslationCoefficientModuleNatTrans C R q A) U :=
  translatedCostructuredCoreTranslationCoefficientNatIso_hom_naturality
    C R q A

-- The unshifted and translated Isos have the promised endpoints.
example (R : AddCommGrpCat.{0}) (p q : ℕ) :
    ((SSet.bkAlternatingBicomplex AddCommGrpCat R
      (SSet.rightCommaNerveDiagram
        (translationProjection (C := C)))).verticalHomologyComplex q).homology p ≅
      (U).obj (coreTranslationActionCoefficientHomology C R q p) :=
  translationBKIteratedHomologyCoefficientIso C R p q

example (R : AddCommGrpCat.{0}) (p q : ℕ) (A : C) :
    ((SSet.bkAlternatingBicomplex AddCommGrpCat R
      (translatedRightCommaNerveDiagram C A)).verticalHomologyComplex q).homology p ≅
      (U).obj (CategoryHomology.homologyWithCoefficients
        (Translation.translateFunctor A ⋙
          coreTranslationCoefficientFunctor C R q) p) :=
  translatedTranslationBKIteratedHomologyCoefficientIso C R p q A

example (R : AddCommGrpCat.{0}) (p q : ℕ) (A : C) :
    HomologicalComplex.homologyMap
          (((HomologicalComplex.homologyFunctor
            AddCommGrpCat c q).mapHomologicalComplex c).map
              (translationBKBicomplexMap C R A)) p ≫
        (translatedTranslationBKIteratedHomologyCoefficientIso
          C R p q A).hom =
      (translationBKIteratedHomologyCoefficientIso C R p q).hom ≫
        (U).map
          ((CategoryHomology.homologyWithCoefficientsFunctor
            (C := Translation C)
            (A := ModuleCat (coreTranslationRing C)) p).map
              (conjugatedFirstTranslationCoefficientModuleNatTrans
                C R q A)) :=
  translationBKIteratedHomologyCoefficientIso_hom_naturality C R p q A

-- Both homological boundary degrees are accepted independently and jointly.
example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) :=
  translationBKIteratedHomologyCoefficientIso_hom_naturality C R 0 q A

example (R : AddCommGrpCat.{0}) (p : ℕ) (A : C) :=
  translationBKIteratedHomologyCoefficientIso_hom_naturality C R p 0 A

example (R : AddCommGrpCat.{0}) (A : C) :=
  translationBKIteratedHomologyCoefficientIso_hom_naturality C R 0 0 A

-- Translation by the zero object is a legitimate boundary input; no
-- unproved claim that its map is definitionally the identity is made.
example (R : AddCommGrpCat.{0}) (p q : ℕ) :=
  translationBKIteratedHomologyCoefficientIso_hom_naturality
    C R p q (0 : C)

-- Identity coefficient transformations exercise the inverse-oriented
-- forget comparison without positivity or nonemptiness assumptions.
example {J A : Type} [Category.{0} J] [CommRing A]
    (M : J ⥤ ModuleCat.{0} A) (n : ℕ) :=
  homologyWithCoefficientsForgetIso_inv_naturality (𝟙 M) n

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C)
    (B : Translation C) :=
  (conjugatedFirstTranslationCoefficientModuleNatTrans
    C R q A).naturality (𝟙 B)

private abbrev ZeroCategory := SingleObj (ZMod 1)

private instance (X Y : ZeroCategory) : Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton (ZMod 1))

private instance : HasZeroObject ZeroCategory where
  zero :=
    ⟨SingleObj.star (ZMod 1),
      (IsZero.iff_id_eq_zero _).2 (Subsingleton.elim _ _)⟩

private instance : HasBinaryBiproducts ZeroCategory where
  has_binary_biproduct X Y := by
    apply hasBinaryBiproduct_of_total
      { pt := SingleObj.star (ZMod 1)
        fst := 0
        snd := 0
        inl := 0
        inr := 0
        inl_fst := Subsingleton.elim _ _
        inl_snd := Subsingleton.elim _ _
        inr_fst := Subsingleton.elim _ _
        inr_snd := Subsingleton.elim _ _ }
    exact Subsingleton.elim _ _

-- Simultaneous zero-category and zero-ring boundary.
example (p q : ℕ) (A : ZeroCategory) :=
  translationBKIteratedHomologyCoefficientIso_hom_naturality
    ZeroCategory (AddCommGrpCat.of (ZMod 1)) p q A

#print axioms translatedCostructuredCoreTranslationCoefficientNatIso_hom_naturality
#print axioms homologyWithCoefficientsForgetIso_inv_naturality
#print axioms translationBKIteratedHomologyCoefficientIso
#print axioms translatedTranslationBKIteratedHomologyCoefficientIso
#print axioms translationBKIteratedHomologyCoefficientIso_hom_naturality

end MathlibExtTest.SInverseSIteratedHomologyActionNaturality

end
