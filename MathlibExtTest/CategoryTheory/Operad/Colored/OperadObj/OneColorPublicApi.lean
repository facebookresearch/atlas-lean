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

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.OneColor

/-!
# Focused O7E one-color operad public-contract packet

Pins the stable downstream-facing contracts for the
one-color comparison of operad objects: colorization and
uncoloring functors with object/map computations, transfer
of the unit and associativity laws both ways, and the
categorical equivalence with its functor/inverse/unit/counit
projections.
-/

open CategoryTheory
open CategoryTheory.Operad

universe w v

variable {V : Type w} [Category.{v} V] [FiniteTensor V]

-- Colorization acts on objects by the object construction.
example (O : OperadObj V) :
    ColoredOperadObj.OneColor.colorizeFunctor.obj O =
      ColoredOperadObj.OneColor.colorizeObj O :=
  ColoredOperadObj.OneColor.colorizeFunctor_obj O

-- Colorization acts on morphisms by the hom construction.
example {O P : OperadObj V} (F : O ⟶ P) :
    ColoredOperadObj.OneColor.colorizeFunctor.map F =
      ColoredOperadObj.OneColor.colorizeHom F :=
  ColoredOperadObj.OneColor.colorizeFunctor_map F

-- Uncoloring acts on objects by the object construction.
example (O : ColoredOperadObj PUnit V) :
    ColoredOperadObj.OneColor.uncolorFunctor.obj O =
      ColoredOperadObj.OneColor.uncolorObj O :=
  ColoredOperadObj.OneColor.uncolorFunctor_obj O

-- Uncoloring acts on morphisms by the hom construction.
example {O P : ColoredOperadObj PUnit V} (F : O ⟶ P) :
    ColoredOperadObj.OneColor.uncolorFunctor.map F =
      ColoredOperadObj.OneColor.uncolorHom F :=
  ColoredOperadObj.OneColor.uncolorFunctor_map F

-- Colorization transfers the right-unit law.
example (O : OperadObj V) :
    ColoredOperadObj.IsRightUnit
      (ColoredOperadObj.OneColor.colorizeCollection
        O.toCollection)
      (ColoredOperadObj.OneColor.colorizeUnit
        O.toCollection O.unit)
      (ColoredOperadObj.OneColor.colorizeSubst
        O.toCollection O.subst) :=
  ColoredOperadObj.OneColor.colorize_isRightUnit O

-- Colorization transfers the left-unit law.
example (O : OperadObj V) :
    ColoredOperadObj.IsLeftUnit
      (ColoredOperadObj.OneColor.colorizeCollection
        O.toCollection)
      (ColoredOperadObj.OneColor.colorizeUnit
        O.toCollection O.unit)
      (ColoredOperadObj.OneColor.colorizeSubst
        O.toCollection O.subst) :=
  ColoredOperadObj.OneColor.colorize_isLeftUnit O

-- Colorization transfers associativity.
example (O : OperadObj V) :
    ColoredOperadObj.IsAssociative
      (ColoredOperadObj.OneColor.colorizeCollection
        O.toCollection)
      (ColoredOperadObj.OneColor.colorizeSubst
        O.toCollection O.subst) :=
  ColoredOperadObj.OneColor.colorize_isAssociative O

-- Uncoloring transfers the right-unit law.
example (O : ColoredOperadObj PUnit V) :
    IsRightUnit
      (ColoredOperadObj.OneColor.uncolorCollection
        O.toCollection)
      (ColoredOperadObj.OneColor.uncolorUnit
        O.toCollection O.unit)
      (ColoredOperadObj.OneColor.uncolorSubst
        O.toCollection O.subst) :=
  ColoredOperadObj.OneColor.uncolor_isRightUnit O

-- Uncoloring transfers the left-unit law.
example (O : ColoredOperadObj PUnit V) :
    IsLeftUnit
      (ColoredOperadObj.OneColor.uncolorCollection
        O.toCollection)
      (ColoredOperadObj.OneColor.uncolorUnit
        O.toCollection O.unit)
      (ColoredOperadObj.OneColor.uncolorSubst
        O.toCollection O.subst) :=
  ColoredOperadObj.OneColor.uncolor_isLeftUnit O

-- Uncoloring transfers associativity.
example (O : ColoredOperadObj PUnit V) :
    IsAssociative
      (ColoredOperadObj.OneColor.uncolorCollection
        O.toCollection)
      (ColoredOperadObj.OneColor.uncolorSubst
        O.toCollection O.subst) :=
  ColoredOperadObj.OneColor.uncolor_isAssociative O

-- The equivalence functor is colorization.
example :
    (ColoredOperadObj.OneColor.operadOneColorEquivalence
      (V := V)).functor =
      ColoredOperadObj.OneColor.colorizeFunctor :=
  ColoredOperadObj.OneColor.operadOneColorEquivalence_functor

-- The equivalence inverse forgets the unique color.
example :
    (ColoredOperadObj.OneColor.operadOneColorEquivalence
      (V := V)).inverse =
      ColoredOperadObj.OneColor.uncolorFunctor :=
  ColoredOperadObj.OneColor.operadOneColorEquivalence_inverse

-- The equivalence unit is the chosen ordinary comparison.
example :
    (ColoredOperadObj.OneColor.operadOneColorEquivalence
      (V := V)).unitIso =
      ColoredOperadObj.OneColor.ordinaryUnitIsoNat :=
  ColoredOperadObj.OneColor.operadOneColorEquivalence_unitIso

-- The equivalence counit is the chosen colored comparison.
example :
    (ColoredOperadObj.OneColor.operadOneColorEquivalence
      (V := V)).counitIso =
      ColoredOperadObj.OneColor.coloredCounitIsoNat :=
  ColoredOperadObj.OneColor.operadOneColorEquivalence_counitIso
