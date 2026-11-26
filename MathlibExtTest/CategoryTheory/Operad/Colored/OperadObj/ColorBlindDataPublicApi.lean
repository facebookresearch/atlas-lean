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

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.ColorBlindData

/-!
# Focused O7E color-blind data public-contract packet

Pins the stable downstream-facing contracts for color-blind
operadic data: the color-ignoring collection, factor/source
comparisons, induced unit/substitution data, and associativity
shape transport.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u v w

variable (Color : Type u)
variable {V : Type w} [Category.{v} V] [FiniteTensor V]

-- Color-ignoring collection.
noncomputable example (O : SymmetricCollection V) :
    ColoredSymmetricCollection Color V :=
  ColoredOperadObj.ColorBlind.collection Color O

-- Factor comparison.
noncomputable example (O : SymmetricCollection V)
    (d : ColoredSubstitutionData Color) :
    (ColoredOperadObj.substitutionFactors
      (ColoredOperadObj.ColorBlind.collection Color O)).obj d ≅
      (substitutionFactors O).obj d.toSubstitutionData :=
  ColoredOperadObj.ColorBlind.factorIso Color O d

-- Natural factor/source comparisons.
noncomputable example (O : SymmetricCollection V) :
    ColoredOperadObj.substitutionFactors
        (ColoredOperadObj.ColorBlind.collection Color O) ≅
      ColoredSubstitutionData.toSubstitutionDataFunctor ⋙
        substitutionFactors O :=
  ColoredOperadObj.ColorBlind.factorNatIso Color O

noncomputable example (O : SymmetricCollection V) :
    ColoredOperadObj.substitutionSource
        (ColoredOperadObj.ColorBlind.collection Color O) ≅
      ColoredSubstitutionData.toSubstitutionDataFunctor ⋙
        substitutionSource O :=
  ColoredOperadObj.ColorBlind.sourceNatIso Color O

example (O : SymmetricCollection V)
    (d : ColoredSubstitutionData Color) :
    (ColoredOperadObj.ColorBlind.sourceNatIso Color O).hom.app d =
      (FiniteTensor.tensor (V := V)).map
        (ColoredOperadObj.ColorBlind.factorHom Color O d) :=
  ColoredOperadObj.ColorBlind.sourceNatIso_hom_app Color O d

-- Induced unit/substitution data.
noncomputable example (O : SymmetricCollection V)
    (η : OperadUnit O) :
    ColoredOperadUnit
      (ColoredOperadObj.ColorBlind.collection Color O) :=
  ColoredOperadObj.ColorBlind.unitData Color O η

noncomputable example (O : SymmetricCollection V)
    (γ : OperadSubstitution O) :
    ColoredOperadSubstitution
      (ColoredOperadObj.ColorBlind.collection Color O) :=
  ColoredOperadObj.ColorBlind.substitutionData Color O γ

-- Associativity shape transport.
noncomputable example (d : ColoredAssocData Color) : AssocData :=
  ColoredOperadObj.ColorBlind.forgetColorsAssocData Color d

example (d : ColoredAssocData Color) :
    (ColoredOperadObj.ColorBlind.forgetColorsAssocData Color d).middleData =
      d.middleData.toSubstitutionData :=
  ColoredOperadObj.ColorBlind.forgetColorsAssocData_middleData Color d

example (d : ColoredAssocData Color) :
    (ColoredOperadObj.ColorBlind.forgetColorsAssocData Color
      d).outerAfterInnerData =
      d.outerAfterInnerData.toSubstitutionData :=
  ColoredOperadObj.ColorBlind.forgetColorsAssocData_outerAfterInnerData Color d

example (d : ColoredAssocData Color) :
    (ColoredOperadObj.ColorBlind.forgetColorsAssocData Color d).innerData =
      d.innerData.toSubstitutionData :=
  ColoredOperadObj.ColorBlind.forgetColorsAssocData_innerData Color d
