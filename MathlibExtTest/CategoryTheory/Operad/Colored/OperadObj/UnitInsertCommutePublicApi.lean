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

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.UnitInsertCommute

/-!
# Unit-insert commutation public-contract packet

Pins the stable downstream-facing contracts of unit-insert
commutation with collection maps: right- and left-unit insertions
commute with unit-preserving maps.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u w v

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

-- Right-unit insertion commutes with unit-preserving maps.
noncomputable example {O P : ColoredSymmetricCollection Color V}
    {ηO : ColoredOperadUnit O} {ηP : ColoredOperadUnit P} (α : O ⟶ P)
    (hη : ∀ c, ηO c ≫
      α.app (ColoredSubstitutionData.unitProfile c) = ηP c)
    (Q : ColoredProfile Color) :
    α.app Q ≫ ColoredOperadObj.rightUnitInsert P ηP Q =
      ColoredOperadObj.rightUnitInsert O ηO Q ≫
        ColoredOperadObj.HomData.sourceHom α
          (ColoredSubstitutionData.rightUnit Q) :=
  by exact ColoredOperadObj.rightUnitInsert_naturality α hη Q

-- Left-unit insertion commutes with unit-preserving maps.
noncomputable example {O P : ColoredSymmetricCollection Color V}
    {ηO : ColoredOperadUnit O} {ηP : ColoredOperadUnit P} (α : O ⟶ P)
    (hη : ∀ c, ηO c ≫
      α.app (ColoredSubstitutionData.unitProfile c) = ηP c)
    (Q : ColoredProfile Color) :
    α.app Q ≫ ColoredOperadObj.leftUnitInsert P ηP Q =
      ColoredOperadObj.leftUnitInsert O ηO Q ≫
        ColoredOperadObj.HomData.sourceHom α
          (ColoredSubstitutionData.leftUnit Q) :=
  by exact ColoredOperadObj.leftUnitInsert_naturality α hη Q
