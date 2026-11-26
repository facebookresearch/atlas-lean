/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.OneColorData

/-!
# Focused O7E one-color data public-contract packet

Pins the stable downstream-facing contracts comparing ordinary
and one-colored operad data: collection round-trips, factor/source
comparisons, and unit/substitution transport.
-/

open CategoryTheory
open CategoryTheory.Operad

universe w v

variable {V : Type w} [Category.{v} V] [FiniteTensor V]

-- Collection round-trips.
noncomputable example (O : SymmetricCollection V) :
    ColoredSymmetricCollection PUnit V :=
  ColoredOperadObj.OneColor.colorizeCollection O

noncomputable example (O : ColoredSymmetricCollection PUnit V) :
    SymmetricCollection V :=
  ColoredOperadObj.OneColor.uncolorCollection O

noncomputable example (O : SymmetricCollection V) :
    O ≅ ColoredOperadObj.OneColor.uncolorCollection
      (ColoredOperadObj.OneColor.colorizeCollection O) :=
  ColoredOperadObj.OneColor.ordinaryCollectionUnitIso O

example (O : SymmetricCollection V) (I : FinBijGroupoid) :
    (ColoredOperadObj.OneColor.ordinaryCollectionUnitIso O).hom.app I =
      𝟙 (O.obj I) :=
  ColoredOperadObj.OneColor.ordinaryCollectionUnitIso_hom_app.{w, v, 0} O I

example (O : SymmetricCollection V) (I : FinBijGroupoid) :
    (ColoredOperadObj.OneColor.ordinaryCollectionUnitIso O).inv.app I =
      𝟙 (O.obj I) :=
  ColoredOperadObj.OneColor.ordinaryCollectionUnitIso_inv_app.{w, v, 0} O I

noncomputable example (O : ColoredSymmetricCollection PUnit V) :
    ColoredOperadObj.OneColor.colorizeCollection
        (ColoredOperadObj.OneColor.uncolorCollection O) ≅ O :=
  ColoredOperadObj.OneColor.coloredCollectionCounitIso O

example (O : ColoredSymmetricCollection PUnit V)
    (P : ColoredProfile PUnit) :
    (ColoredOperadObj.OneColor.coloredCollectionCounitIso O).hom.app P =
      O.map (ColoredProfile.oneColorCounitHom P) :=
  ColoredOperadObj.OneColor.coloredCollectionCounitIso_hom_app O P

example (O : ColoredSymmetricCollection PUnit V)
    (P : ColoredProfile PUnit) :
    (ColoredOperadObj.OneColor.coloredCollectionCounitIso O).inv.app P =
      O.map (Groupoid.inv (ColoredProfile.oneColorCounitHom P)) :=
  ColoredOperadObj.OneColor.coloredCollectionCounitIso_inv_app O P

-- Colorize source comparison.
example (O : SymmetricCollection V)
    (d : ColoredSubstitutionData PUnit) :
    (ColoredOperadObj.OneColor.colorizeSourceNatIso O).hom.app d =
      (FiniteTensor.tensor (V := V)).map
        (ColoredOperadObj.OneColor.colorizeFactorHom O d) :=
  ColoredOperadObj.OneColor.colorizeSourceNatIso_hom_app O d

-- Uncolor factor/source comparisons.
noncomputable example (O : ColoredSymmetricCollection PUnit V)
    (d : SubstitutionData) :
    (substitutionFactors
      (ColoredOperadObj.OneColor.uncolorCollection O)).obj d ≅
      (ColoredOperadObj.substitutionFactors O).obj
        (ColoredSubstitutionData.oneColorFunctor.obj d) :=
  ColoredOperadObj.OneColor.uncolorFactorIso O d

noncomputable example (O : ColoredSymmetricCollection PUnit V) :
    substitutionFactors
        (ColoredOperadObj.OneColor.uncolorCollection O) ≅
      ColoredSubstitutionData.oneColorFunctor ⋙
        ColoredOperadObj.substitutionFactors O :=
  ColoredOperadObj.OneColor.uncolorFactorNatIso O

noncomputable example (O : ColoredSymmetricCollection PUnit V) :
    substitutionSource
        (ColoredOperadObj.OneColor.uncolorCollection O) ≅
      ColoredSubstitutionData.oneColorFunctor ⋙
        ColoredOperadObj.substitutionSource O :=
  ColoredOperadObj.OneColor.uncolorSourceNatIso O

example (O : ColoredSymmetricCollection PUnit V)
    (d : SubstitutionData) :
    (ColoredOperadObj.OneColor.uncolorSourceNatIso O).hom.app d =
      (FiniteTensor.tensor (V := V)).map
        (ColoredOperadObj.OneColor.uncolorFactorHom O d) :=
  ColoredOperadObj.OneColor.uncolorSourceNatIso_hom_app O d

-- Unit/substitution transport.
noncomputable example (O : SymmetricCollection V)
    (η : OperadUnit O) :
    ColoredOperadUnit
      (ColoredOperadObj.OneColor.colorizeCollection O) :=
  ColoredOperadObj.OneColor.colorizeUnit O η

noncomputable example (O : SymmetricCollection V)
    (γ : OperadSubstitution O) :
    ColoredOperadSubstitution
      (ColoredOperadObj.OneColor.colorizeCollection O) :=
  ColoredOperadObj.OneColor.colorizeSubst O γ

example (O : SymmetricCollection V) (γ : OperadSubstitution O)
    (d : ColoredSubstitutionData PUnit) :
    (ColoredOperadObj.OneColor.colorizeSubst O γ).app d =
      (ColoredOperadObj.OneColor.colorizeSourceNatIso O).hom.app d ≫
        γ.app (ColoredSubstitutionData.forgetOneColorFunctor.obj d) :=
  ColoredOperadObj.OneColor.colorizeSubst_app O γ d

noncomputable example (O : ColoredSymmetricCollection PUnit V)
    (η : ColoredOperadUnit O) :
    OperadUnit (ColoredOperadObj.OneColor.uncolorCollection O) :=
  ColoredOperadObj.OneColor.uncolorUnit O η

noncomputable example (O : ColoredSymmetricCollection PUnit V)
    (γ : ColoredOperadSubstitution O) :
    OperadSubstitution
      (ColoredOperadObj.OneColor.uncolorCollection O) :=
  ColoredOperadObj.OneColor.uncolorSubst O γ

example (O : ColoredSymmetricCollection PUnit V)
    (γ : ColoredOperadSubstitution O) (d : SubstitutionData) :
    (ColoredOperadObj.OneColor.uncolorSubst O γ).app d =
      (ColoredOperadObj.OneColor.uncolorSourceNatIso O).hom.app d ≫
        γ.app (ColoredSubstitutionData.oneColorFunctor.obj d) :=
  ColoredOperadObj.OneColor.uncolorSubst_app O γ d

-- Unit-data transport.
example (I : FintypeCat) :
    ColoredSubstitutionData.oneColorFunctor.obj (rightUnitData I) =
      ColoredSubstitutionData.rightUnit
        (ColoredProfile.oneColorFunctor.obj ⟨I⟩) :=
  ColoredOperadObj.OneColor.oneColorFunctor_obj_rightUnitData I

example (I : FintypeCat) :
    ColoredSubstitutionData.oneColorFunctor.obj (leftUnitData I) =
      ColoredSubstitutionData.leftUnit
        (ColoredProfile.oneColorFunctor.obj ⟨I⟩) :=
  ColoredOperadObj.OneColor.oneColorFunctor_obj_leftUnitData I

example (P : ColoredProfile PUnit) :
    ColoredSubstitutionData.forgetOneColorFunctor.obj
        (ColoredSubstitutionData.rightUnit P) =
      rightUnitData P.inputs :=
  ColoredOperadObj.OneColor.forgetOneColorFunctor_obj_rightUnit P

example (P : ColoredProfile PUnit) :
    ColoredSubstitutionData.forgetOneColorFunctor.obj
        (ColoredSubstitutionData.leftUnit P) =
      leftUnitData P.inputs :=
  ColoredOperadObj.OneColor.forgetOneColorFunctor_obj_leftUnit P

-- Associativity-data transport.
noncomputable example (d : AssocData) : ColoredAssocData PUnit :=
  ColoredOperadObj.OneColor.colorizeAssocData d

example (d : AssocData) :
    (ColoredOperadObj.OneColor.colorizeAssocData d).middleData =
      ColoredSubstitutionData.oneColorFunctor.obj d.middleData :=
  ColoredOperadObj.OneColor.colorizeAssocData_middleData d

example (d : AssocData) :
    (ColoredOperadObj.OneColor.colorizeAssocData d).outerAfterInnerData =
      ColoredSubstitutionData.oneColorFunctor.obj
        d.outerAfterInnerData :=
  ColoredOperadObj.OneColor.colorizeAssocData_outerAfterInnerData d

example (d : AssocData) :
    (ColoredOperadObj.OneColor.colorizeAssocData d).innerData =
      ColoredSubstitutionData.oneColorFunctor.obj d.innerData :=
  ColoredOperadObj.OneColor.colorizeAssocData_innerData d

noncomputable example (d : ColoredAssocData PUnit) : AssocData :=
  ColoredOperadObj.OneColor.uncolorAssocData d

example (d : ColoredAssocData PUnit) :
    (ColoredOperadObj.OneColor.uncolorAssocData d).middleData =
      ColoredSubstitutionData.forgetOneColorFunctor.obj d.middleData :=
  ColoredOperadObj.OneColor.uncolorAssocData_middleData d

example (d : ColoredAssocData PUnit) :
    (ColoredOperadObj.OneColor.uncolorAssocData d).outerAfterInnerData =
      ColoredSubstitutionData.forgetOneColorFunctor.obj
        d.outerAfterInnerData :=
  ColoredOperadObj.OneColor.uncolorAssocData_outerAfterInnerData d

example (d : ColoredAssocData PUnit) :
    (ColoredOperadObj.OneColor.uncolorAssocData d).innerData =
      ColoredSubstitutionData.forgetOneColorFunctor.obj d.innerData :=
  ColoredOperadObj.OneColor.uncolorAssocData_innerData d
