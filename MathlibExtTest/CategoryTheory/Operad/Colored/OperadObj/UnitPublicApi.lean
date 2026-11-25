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

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Unit

/-!
# Focused O7E colored unit-foundation public-contract packet

Pins the stable downstream-facing contracts for colored operadic
unit and substitution data: the color-indexed unit type and the
substitution natural-transformation type.
-/

open CategoryTheory
open CategoryTheory.Operad

universe w v u

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

-- Color-indexed unit unfolding.
example (O : ColoredSymmetricCollection Color V) :
    ColoredOperadUnit O =
      ((c : Color) → operadUnitSource (V := V) ⟶
        O.obj (ColoredSubstitutionData.unitProfile c)) :=
  rfl

-- Substitution type unfolding.
example (O : ColoredSymmetricCollection Color V) :
    ColoredOperadSubstitution O =
      (ColoredOperadObj.substitutionSource O ⟶
        ColoredOperadObj.substitutionTarget O) :=
  rfl
