/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Dual.ODual

import Mathlib.Algebra.Polynomial.AlgebraMap

#check @Module.ODual
#check @Module.ODual.smul_apply
#check @Module.ODual.homEquiv
#check @Module.ODual.homEquiv_apply
#check @Module.ODual.homEquiv_symm_apply_apply
#check @Module.ODual.dualMap
#check @Module.ODual.homEquiv_comp
#check @Module.ODual.homEquivOfLinearEquiv
#check @Module.ODual.homEquivOfLinearEquiv_apply

-- For `A = ℚ[X]` over `O = ℚ`, the `A`-action on `ℚ`-linear forms precomposes with
-- multiplication.
example (φ : Module.ODual ℚ (Polynomial ℚ) (Polynomial ℚ)) (a x : Polynomial ℚ) :
    (a • φ) x = φ (a * x) :=
  Module.ODual.smul_apply a φ x

-- `Φ` and its inverse are mutually inverse on values.
example {O A M : Type*} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup M] [Module A M]
    [Module O M] [IsScalarTower O A M] (φ : Module.ODual O A M) (m : M) :
    Module.ODual.homEquiv M ((Module.ODual.homEquiv M).symm φ) m = φ m := by
  simp
