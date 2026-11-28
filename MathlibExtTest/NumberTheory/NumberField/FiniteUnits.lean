/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.FiniteUnits

/-!
# Tests for the finiteness of the unit group of an imaginary quadratic field
-/

set_option autoImplicit false

@[expose] public section

open NumberField
open scoped NumberField

namespace MathlibExtTest.NumberTheory.FiniteUnits

/-- An imaginary quadratic field has finitely many units in its ring of integers. -/
example (F : Type*) [Field F] [NumberField F] [IsTotallyComplex F]
    (hF : Module.finrank ℚ F = 2) : Finite (𝓞 F)ˣ :=
  NumberField.Units.finite_of_finrank_eq_two hF

#check @NumberField.Units.finite_of_finrank_eq_two

end MathlibExtTest.NumberTheory.FiniteUnits
