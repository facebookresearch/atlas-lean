/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.WeightedDirichletConvolution
import Mathlib.Algebra.Order.Floor.Semifield

open ArithmeticFunction Finset MetaMathlibExt
open scoped ArithmeticFunction.Moebius

-- Below the first positive integer, the expansion vanishes for every choice of weights.
example (w u v : ArithmeticFunction ℂ) {x : ℝ} (hx : x < 1) :
    (∑ r ∈ Icc 1 ⌊x⌋₊, (w * (μ : ArithmeticFunction ℂ)) r *
      ∑ j ∈ Icc 1 ⌊x / r⌋₊, (u * v) (r * j)) = 0 := by
  rw [← sum_mul_dirichletConvolution_eq_sum_moebius]
  simp [Nat.floor_eq_zero.mpr hx]

-- At 5/2 the divisor 1 contributes both terms, while the divisor 2 contributes only the second.
example (w u v : ArithmeticFunction ℂ) :
    w 1 * (u * v) 1 + w 2 * (u * v) 2 =
      (w * (μ : ArithmeticFunction ℂ)) 1 * ((u * v) 1 + (u * v) 2) +
      (w * (μ : ArithmeticFunction ℂ)) 2 * (u * v) 2 := by
  have h := sum_mul_dirichletConvolution_eq_sum_moebius w u v (5 / 2)
  have hfloor : ⌊(5 : ℝ) / 2⌋₊ = 2 := Nat.floor_div_eq_div 5 2
  have hIcc : Icc 1 2 = {1, 2} := by decide
  simpa [Nat.floor_div_natCast, hfloor, hIcc] using h
