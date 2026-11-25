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

import MathlibExt.CategoryTheory.Operad.OperadObj.Basic

/-!
# Focused O7E operad-object public-contract packet

Pins the stable downstream-facing contracts for enriched
one-colored operads: the underlying data and law projections.
-/

open CategoryTheory
open CategoryTheory.Operad

universe v u

variable {V : Type u} [Category.{v} V] [FiniteTensor V]

-- Underlying collection projection.
noncomputable example (O : OperadObj V) : SymmetricCollection V :=
  O.toCollection

-- Unit projection.
noncomputable example (O : OperadObj V) :
    OperadUnit O.toCollection :=
  O.unit

-- Substitution projection.
noncomputable example (O : OperadObj V) :
    OperadSubstitution O.toCollection :=
  O.subst

-- Law projections.
example (O : OperadObj V) :
    IsRightUnit O.toCollection O.unit O.subst :=
  O.right_unit

example (O : OperadObj V) :
    IsLeftUnit O.toCollection O.unit O.subst :=
  O.left_unit

example (O : OperadObj V) :
    IsAssociative O.toCollection O.subst :=
  O.assoc
