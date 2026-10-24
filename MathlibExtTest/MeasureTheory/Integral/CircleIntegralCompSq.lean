/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import MathlibExt.MeasureTheory.Integral.CircleIntegralCompSq

set_option autoImplicit false

-- The book's statement: `∮_{|z| = r} R(z²) dz = 0` for a rational function `R`.
example (R : RatFunc ℂ) (r : ℝ) :
    (∮ z in C(0, r), R.eval (RingHom.id ℂ) (z ^ 2)) = 0 :=
  circleIntegral_comp_sq_eq_zero (fun w => R.eval (RingHom.id ℂ) w) r

-- For example `∮_{|z| = 1} dz / (z² - 4) = 0`.
example : (∮ z in C(0, 1), (z ^ 2 - 4)⁻¹) = 0 :=
  circleIntegral_comp_sq_eq_zero (fun w => (w - 4)⁻¹) 1

#print axioms circleIntegral_comp_sq_eq_zero
