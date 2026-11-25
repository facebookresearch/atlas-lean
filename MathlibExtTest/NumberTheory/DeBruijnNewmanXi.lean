/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DeBruijnNewmanXi

open Complex MathlibExt.NumberTheory.DeBruijnNewman MathlibExt.NumberTheory.DeBruijnNewmanXiWanted
open RiemannXi

example (z : ℂ) : 8 * H 0 z = riemannXi (1 / 2 + I * z / 2) :=
  eight_mul_H_zero_eq_riemannXi z

-- The arguments I and -I take xi to the regularized values at 0 and 1.
example : H 0 I = 1 / 16 := by
  have h := eight_mul_H_zero_eq_riemannXi I
  rw [I_mul_I, show (1 / 2 : ℂ) + -1 / 2 = 0 by ring] at h
  simp [riemannXi] at h
  linear_combination h / 8

example : H 0 (-I) = 1 / 16 := by
  have h := eight_mul_H_zero_eq_riemannXi (-I)
  rw [mul_neg, I_mul_I, neg_neg, show (1 / 2 : ℂ) + 1 / 2 = 1 by ring] at h
  simp [riemannXi] at h
  linear_combination h / 8
