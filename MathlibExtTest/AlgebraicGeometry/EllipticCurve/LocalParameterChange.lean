/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.LocalParameterChange
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum

open WeierstrassCurve.LocalParameter

#check @leadingCoeff_mul_parameter
#check @cube_eq_sq_iff_of_isUnit

/-- Concrete instance with `A = K = R = ℚ` and the identity restriction: `t = 2`, `x = 3 / 4`,
`y = 5 / 8`, and the new parameter `t' = 3 t`. -/
example : (algebraMap ℚ ℚ (3 * 2)) ^ 2 * (3 / 4 : ℚ) = algebraMap ℚ ℚ (3 ^ 2 * 3) ∧
    (algebraMap ℚ ℚ (3 * 2)) ^ 3 * (5 / 8 : ℚ) = algebraMap ℚ ℚ (3 ^ 3 * 5) ∧
    (RingHom.id ℚ) (3 ^ 2 * 3) = (RingHom.id ℚ) 3 ^ 2 * (RingHom.id ℚ) 3 ∧
    (RingHom.id ℚ) (3 ^ 3 * 5) = (RingHom.id ℚ) 3 ^ 3 * (RingHom.id ℚ) 5 :=
  leadingCoeff_mul_parameter (RingHom.id ℚ) (t := 2) (a := 3) (b := 5) (by norm_num)
    (by norm_num)

/-- The condition `v³ = v'²` for `v = 4`, `v' = 8` survives the unit `u = -1` of `ℤ`. -/
example : ((-1 : ℤ) ^ 2 * 4) ^ 3 = ((-1) ^ 3 * 8) ^ 2 :=
  (cube_eq_sq_iff_of_isUnit isUnit_one.neg 4 8).mpr (by norm_num)
