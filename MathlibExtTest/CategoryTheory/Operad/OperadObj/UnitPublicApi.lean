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

import MathlibExt.CategoryTheory.Operad.OperadObj.Unit

/-!
# Focused O7E unit-foundation public-contract packet

Pins the stable downstream-facing contracts for the operadic unit
foundation: the unit source and the unit morphism type.
-/

open CategoryTheory
open CategoryTheory.Operad

universe v u

variable {V : Type u} [Category.{v} V] [FiniteTensor V]

-- Unit source signature.
noncomputable example : V :=
  operadUnitSource (V := V)

-- Unit morphism type unfolding.
example (O : SymmetricCollection V) :
    OperadUnit O = (operadUnitSource (V := V) ⟶ O.eval arityOne) :=
  rfl
