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

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.ColorBlindUnit

/-!
# Focused O7E color-blind unit public-contract packet

Pins the stable downstream-facing contracts comparing
color-blind and ordinary unit insertions: the right- and
left-insertion compatibilities.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u v w

variable (Color : Type u)
variable {V : Type w} [Category.{v} V] [FiniteTensor V]

-- Right insertion compatibility.
example (O : SymmetricCollection V) (η : OperadUnit O)
    (P : ColoredProfile Color) :
    ColoredOperadObj.rightUnitInsert
          (ColoredOperadObj.ColorBlind.collection Color O)
          (ColoredOperadObj.ColorBlind.unitData Color O η) P ≫
        (ColoredOperadObj.ColorBlind.sourceNatIso Color O).hom.app
          (ColoredSubstitutionData.rightUnit P) =
      rightUnitInsert O η P.inputs :=
  ColoredOperadObj.ColorBlind.rightUnitInsert_compat Color O η P

-- Left insertion compatibility.
example (O : SymmetricCollection V) (η : OperadUnit O)
    (P : ColoredProfile Color) :
    ColoredOperadObj.leftUnitInsert
          (ColoredOperadObj.ColorBlind.collection Color O)
          (ColoredOperadObj.ColorBlind.unitData Color O η) P ≫
        (ColoredOperadObj.ColorBlind.sourceNatIso Color O).hom.app
          (ColoredSubstitutionData.leftUnit P) =
      leftUnitInsert O η P.inputs :=
  ColoredOperadObj.ColorBlind.leftUnitInsert_compat Color O η P
