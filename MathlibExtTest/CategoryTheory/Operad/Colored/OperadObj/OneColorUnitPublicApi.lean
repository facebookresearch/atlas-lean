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

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.OneColorUnit

/-!
# Focused O7E one-color unit public-contract packet

Pins the stable downstream-facing contracts comparing ordinary
and one-colored unit insertions: identity outer maps and the
colorize/uncolor insertion compatibilities.
-/

open CategoryTheory
open CategoryTheory.Operad

universe w v

variable {V : Type w} [Category.{v} V] [FiniteTensor V]

-- Colorized outer-profile maps are identities.
example (I : FintypeCat) :
    ColoredSubstitutionData.rightUnitOuterHom
        (ColoredProfile.oneColorFunctor.obj ⟨I⟩) =
      𝟙 (ColoredProfile.oneColorFunctor.obj ⟨I⟩) :=
  ColoredOperadObj.OneColor.rightUnitOuterHom_oneColor I

example (I : FintypeCat) :
    ColoredSubstitutionData.leftUnitOuterHom
        (ColoredProfile.oneColorFunctor.obj ⟨I⟩) =
      𝟙 (ColoredSubstitutionData.unitProfile PUnit.unit) :=
  ColoredOperadObj.OneColor.leftUnitOuterHom_oneColor I

-- Colorize insertion compatibilities.
example (O : SymmetricCollection V) (η : OperadUnit O)
    (P : ColoredProfile PUnit) :
    ColoredOperadObj.rightUnitInsert
          (ColoredOperadObj.OneColor.colorizeCollection O)
          (ColoredOperadObj.OneColor.colorizeUnit O η) P ≫
        (ColoredOperadObj.OneColor.colorizeSourceNatIso O).hom.app
          (ColoredSubstitutionData.rightUnit P) =
      rightUnitInsert O η P.inputs :=
  ColoredOperadObj.OneColor.colorize_rightUnitInsert O η P

example (O : SymmetricCollection V) (η : OperadUnit O)
    (P : ColoredProfile PUnit) :
    ColoredOperadObj.leftUnitInsert
          (ColoredOperadObj.OneColor.colorizeCollection O)
          (ColoredOperadObj.OneColor.colorizeUnit O η) P ≫
        (ColoredOperadObj.OneColor.colorizeSourceNatIso O).hom.app
          (ColoredSubstitutionData.leftUnit P) =
      leftUnitInsert O η P.inputs :=
  ColoredOperadObj.OneColor.colorize_leftUnitInsert O η P

-- Uncolor insertion compatibilities.
example (O : ColoredSymmetricCollection PUnit V)
    (η : ColoredOperadUnit O) (I : FintypeCat) :
    rightUnitInsert
          (ColoredOperadObj.OneColor.uncolorCollection O)
          (ColoredOperadObj.OneColor.uncolorUnit O η) I ≫
        (ColoredOperadObj.OneColor.uncolorSourceNatIso O).hom.app
          (rightUnitData I) =
      ColoredOperadObj.rightUnitInsert O η
        (ColoredProfile.oneColorFunctor.obj ⟨I⟩) :=
  ColoredOperadObj.OneColor.uncolor_rightUnitInsert O η I

example (O : ColoredSymmetricCollection PUnit V)
    (η : ColoredOperadUnit O) (I : FintypeCat) :
    leftUnitInsert
          (ColoredOperadObj.OneColor.uncolorCollection O)
          (ColoredOperadObj.OneColor.uncolorUnit O η) I ≫
        (ColoredOperadObj.OneColor.uncolorSourceNatIso O).hom.app
          (leftUnitData I) =
      ColoredOperadObj.leftUnitInsert O η
        (ColoredProfile.oneColorFunctor.obj ⟨I⟩) :=
  ColoredOperadObj.OneColor.uncolor_leftUnitInsert O η I
