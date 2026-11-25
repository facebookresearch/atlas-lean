/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import all MathlibExt.CategoryTheory.Monoidal.SymmetricTensorPower
import Mathlib.CategoryTheory.Monoidal.Types.Basic

set_option autoImplicit false

noncomputable section

open CategoryTheory.MonoidalCategory.TensorPower

namespace MathlibExtTest.SymmetricTensorPowerImplementationTests

/-- Six pairwise distinct coordinates in the actual left-associated carrier. -/
private def distantSwapInput : tensorPowObj (Fin 6) 6 :=
  ((((((PUnit.unit, 0), 1), 2), 3), 4), 5)

/-- The load-bearing internal star transposition reduces on a moderate-size
concrete tensor power, so this checks its construction rather than a law. -/
example :
    (CategoryTheory.MonoidalCategory.SymmetricTensorPower.moveZeroIso
      (Fin 6) 6 (5 : Fin 6)).hom distantSwapInput =
        ((((((PUnit.unit, 5), 1), 2), 3), 4), 0) := by
  rfl

#print axioms
  CategoryTheory.MonoidalCategory.SymmetricTensorPower.moveZeroIso

end MathlibExtTest.SymmetricTensorPowerImplementationTests
