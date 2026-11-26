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

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.ColorBlind

/-!
# Focused O7E color-blind lift public-contract packet

Pins the stable downstream-facing contracts for the color-blind
lift from ordinary to colored operads: factor and source
naturality in collection morphisms, the functor object/map
computations, and transfer of the right-unit, left-unit, and
associativity laws.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u v w

variable (Color : Type u)
variable {V : Type w} [Category.{v} V] [FiniteTensor V]

-- The factor comparison is natural in collection morphisms.
example {O P : SymmetricCollection V} (α : O ⟶ P)
    (d : ColoredSubstitutionData Color) :
    ColoredOperadObj.HomData.factorHom
          (Functor.whiskerLeft
            (ColoredProfile.arityFunctor Color) α) d ≫
        ColoredOperadObj.ColorBlind.factorHom Color P d =
      ColoredOperadObj.ColorBlind.factorHom Color O d ≫
        OperadObj.HomData.factorHom α
          (ColoredSubstitutionData.toSubstitutionDataFunctor.obj
            d) :=
  ColoredOperadObj.ColorBlind.factorHom_naturality
    Color α d

-- The source comparison is natural in collection morphisms.
example {O P : SymmetricCollection V} (α : O ⟶ P)
    (d : ColoredSubstitutionData Color) :
    ColoredOperadObj.HomData.sourceHom
          (Functor.whiskerLeft
            (ColoredProfile.arityFunctor Color) α) d ≫
        (ColoredOperadObj.ColorBlind.sourceNatIso Color P).hom.app
          d =
      (ColoredOperadObj.ColorBlind.sourceNatIso Color O).hom.app
          d ≫
        OperadObj.HomData.sourceHom α
          (ColoredSubstitutionData.toSubstitutionDataFunctor.obj
            d) :=
  ColoredOperadObj.ColorBlind.sourceHom_naturality
    Color α d

-- The lift acts on objects by the object construction.
example (O : OperadObj V) :
    (ColoredOperadObj.ColorBlind.functor Color).obj O =
      ColoredOperadObj.ColorBlind.obj Color O :=
  ColoredOperadObj.ColorBlind.functor_obj Color O

-- The lift acts on morphisms by the hom construction.
example {O P : OperadObj V} (F : O ⟶ P) :
    (ColoredOperadObj.ColorBlind.functor Color).map F =
      ColoredOperadObj.ColorBlind.hom Color F :=
  ColoredOperadObj.ColorBlind.functor_map Color F

-- The lift transfers the right-unit law.
example (O : OperadObj V) :
    ColoredOperadObj.IsRightUnit
      (ColoredOperadObj.ColorBlind.collection Color
        O.toCollection)
      (ColoredOperadObj.ColorBlind.unitData Color
        O.toCollection O.unit)
      (ColoredOperadObj.ColorBlind.substitutionData Color
        O.toCollection O.subst) :=
  ColoredOperadObj.ColorBlind.isRightUnit Color O

-- The lift transfers the left-unit law.
example (O : OperadObj V) :
    ColoredOperadObj.IsLeftUnit
      (ColoredOperadObj.ColorBlind.collection Color
        O.toCollection)
      (ColoredOperadObj.ColorBlind.unitData Color
        O.toCollection O.unit)
      (ColoredOperadObj.ColorBlind.substitutionData Color
        O.toCollection O.subst) :=
  ColoredOperadObj.ColorBlind.isLeftUnit Color O

-- The lift transfers associativity.
example (O : OperadObj V) :
    ColoredOperadObj.IsAssociative
      (ColoredOperadObj.ColorBlind.collection Color
        O.toCollection)
      (ColoredOperadObj.ColorBlind.substitutionData Color
        O.toCollection O.subst) :=
  ColoredOperadObj.ColorBlind.isAssociative Color O
