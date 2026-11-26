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

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Basic

/-!
# Focused O7E colored operad-object public-contract packet

Pins the stable downstream-facing contracts for enriched colored
operads: the underlying data and law projections.
-/

open CategoryTheory
open CategoryTheory.Operad

universe w v u

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

-- Underlying collection projection.
noncomputable example (O : ColoredOperadObj Color V) :
    ColoredSymmetricCollection Color V :=
  O.toCollection

-- Unit projection.
noncomputable example (O : ColoredOperadObj Color V) :
    ColoredOperadUnit O.toCollection :=
  O.unit

-- Substitution projection.
noncomputable example (O : ColoredOperadObj Color V) :
    ColoredOperadSubstitution O.toCollection :=
  O.subst

-- Law projections.
example (O : ColoredOperadObj Color V) :
    ColoredOperadObj.IsRightUnit O.toCollection O.unit O.subst :=
  O.right_unit

example (O : ColoredOperadObj Color V) :
    ColoredOperadObj.IsLeftUnit O.toCollection O.unit O.subst :=
  O.left_unit

example (O : ColoredOperadObj Color V) :
    ColoredOperadObj.IsAssociative O.toCollection O.subst :=
  O.assoc
