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

import MathlibExt.CategoryTheory.Operad.FiniteSet.Basic

/-!
# Focused O7E set-operad basic public-contract packet

Pins the stable downstream-facing contracts for set operads:
the `SetOperad` alias as the Cartesian finite-tensor
specialization of `OperadObj`, and the morphism alias.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u

-- Set operads are type-valued operad objects.
example : SetOperad.{u} = OperadObj (Type u) :=
  rfl

-- Set-operad homs are operad-object homs.
example (O P : SetOperad.{u}) :
    SetOperadHom O P = OperadObj.Hom O P :=
  rfl
