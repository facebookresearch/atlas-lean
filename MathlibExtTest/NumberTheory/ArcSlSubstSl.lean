/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArcSlSubstSl

open MetaMathlibExt PowerSeries

variable (S C : PowerSeries ℚ)
    (hS : derivative S = C ^ 2) (hC : derivative C = -(S ^ 2))
    (hS0 : constantCoeff S = 0) (hC0 : constantCoeff C = 1)

-- Substituting Sl into ArcSl gives the variable.
example : (PowerSeries.mk fun k => if k % 3 = 1 then
      (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0).subst S =
    PowerSeries.X :=
  arcSl_subst_sl S C hS hC hS0 hC0

-- Hence the linear coefficient of the composition is one.
example : coeff 1
    ((PowerSeries.mk fun k => if k % 3 = 1 then
      (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0).subst S) = 1 := by
  rw [arcSl_subst_sl S C hS hC hS0 hC0]
  simp

-- And the coefficient of degree four of the composition vanishes.
example : coeff 4
    ((PowerSeries.mk fun k => if k % 3 = 1 then
      (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0).subst S) = 0 := by
  rw [arcSl_subst_sl S C hS hC hS0 hC0, coeff_X]
  norm_num

-- Differentiating the identity gives the derivative of the composition.
example : derivative ((PowerSeries.mk fun k => if k % 3 = 1 then
      (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0).subst S) = 1 := by
  rw [arcSl_subst_sl S C hS hC hS0 hC0]
  simp

-- The first nonlinear coefficient of ArcSl itself is `1 / 6`.
example : coeff 4 (PowerSeries.mk fun k => if k % 3 = 1 then
      (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0) = 1 / 6 := by
  rw [coeff_mk]
  norm_num [Ring.choose_one_right]
