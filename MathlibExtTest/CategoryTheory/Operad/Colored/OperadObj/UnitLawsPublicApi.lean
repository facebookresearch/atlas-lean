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

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.UnitLaws

/-!
# Focused O7E colored unit-laws public-contract packet

Pins the stable downstream-facing contracts for colored operadic unit
laws: the right/left factor homs, insertion maps, and the two unit-law
equations.
-/

open CategoryTheory
open CategoryTheory.Operad

universe w v u

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

-- Right factor hom signature.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (η : ColoredOperadUnit O) (P : ColoredProfile Color) :
    ColoredOperadObj.UnitInsertion.rightTensorFamily O P ⟶
      (ColoredOperadObj.substitutionFactors O).obj
        (ColoredSubstitutionData.rightUnit P) :=
  ColoredOperadObj.UnitInsertion.rightFactorHom O η P

-- Left factor hom signature.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (η : ColoredOperadUnit O) (P : ColoredProfile Color) :
    ColoredOperadObj.UnitInsertion.leftTensorFamily O P ⟶
      (ColoredOperadObj.substitutionFactors O).obj
        (ColoredSubstitutionData.leftUnit P) :=
  ColoredOperadObj.UnitInsertion.leftFactorHom O η P

-- Right insertion signature.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (η : ColoredOperadUnit O) (P : ColoredProfile Color) :
    O.obj P ⟶ (ColoredOperadObj.substitutionSource O).obj
      (ColoredSubstitutionData.rightUnit P) :=
  ColoredOperadObj.rightUnitInsert O η P

-- Left insertion signature.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (η : ColoredOperadUnit O) (P : ColoredProfile Color) :
    O.obj P ⟶ (ColoredOperadObj.substitutionSource O).obj
      (ColoredSubstitutionData.leftUnit P) :=
  ColoredOperadObj.leftUnitInsert O η P

-- Right unit-law equation.
example (O : ColoredSymmetricCollection Color V)
    (η : ColoredOperadUnit O) (γ : ColoredOperadSubstitution O)
    (h : ColoredOperadObj.IsRightUnit O η γ)
    (P : ColoredProfile Color) :
    ColoredOperadObj.rightUnitInsert O η P ≫
        γ.app (ColoredSubstitutionData.rightUnit P) ≫
        O.map (ColoredSubstitutionData.rightUnitTotalHom P) =
      𝟙 (O.obj P) :=
  h P

-- Left unit-law equation.
example (O : ColoredSymmetricCollection Color V)
    (η : ColoredOperadUnit O) (γ : ColoredOperadSubstitution O)
    (h : ColoredOperadObj.IsLeftUnit O η γ)
    (P : ColoredProfile Color) :
    ColoredOperadObj.leftUnitInsert O η P ≫
        γ.app (ColoredSubstitutionData.leftUnit P) ≫
        O.map (ColoredSubstitutionData.leftUnitTotalHom P) =
      𝟙 (O.obj P) :=
  h P
