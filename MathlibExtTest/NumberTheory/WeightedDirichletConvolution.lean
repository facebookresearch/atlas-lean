/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WeightedDirichletConvolution
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Tests for weighted summation of Dirichlet convolutions

These tests derive boundary cases and a nonintegral specialization of the weighted summation
formula.

Reference: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Theorem 1, Equation (8).
-/

namespace MathlibExtTest.NumberTheory.WeightedDirichletConvolution

open ArithmeticFunction Finset MetaMathlibExt
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

open scoped Classical in
example {u v : ArithmeticFunction ℂ} (hu : u.IsCompletelyMultiplicative)
    (hv : v.IsCompletelyMultiplicative) (w : ArithmeticFunction ℂ) {x : ℝ} (hx : x < 1) :
    (∑ r ∈ Icc 1 ⌊x⌋₊, (w * (μ : ArithmeticFunction ℂ)) r *
      ∑ d ∈ r.divisors, u d * v (r / d) * ∑ m ∈ d.divisors, (μ m : ℂ) * v m *
        ∑ j ∈ Icc 1 ⌊x / (m * r)⌋₊, (u * v) j) = 0 := by
  rw [← weighted_sum_dirichletConvolution_eq hu hv]
  simp [Nat.floor_eq_zero.mpr hx]

private theorem zeta_completelyMultiplicative :
    (ζ : ArithmeticFunction ℂ).IsCompletelyMultiplicative := by
  intro m n
  by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [natCoe_apply, hm, hn]

open scoped Classical in
example (w : ArithmeticFunction ℂ) :
    w 1 + 2 * w 2 = 3 * (w * (μ : ArithmeticFunction ℂ)) 1 +
      2 * (w * (μ : ArithmeticFunction ℂ)) 2 := by
  have h := weighted_sum_dirichletConvolution_eq zeta_completelyMultiplicative
    zeta_completelyMultiplicative w (5 / 2)
  have hfloor : ⌊(5 : ℝ) / 2⌋₊ = 2 := Nat.floor_div_eq_div 5 2
  have hIcc : Icc 1 2 = {1, 2} := by decide
  have hdiv : (2 : ℕ).divisors = {1, 2} := by decide
  have hz1 : ((ζ : ArithmeticFunction ℂ) * ζ) 1 = 1 := by simp [natCoe_apply]
  have hz2 : ((ζ : ArithmeticFunction ℂ) * ζ) 2 = 2 := by
    rw [coe_mul_zeta_apply]
    norm_num [hdiv, natCoe_apply]
  norm_num [-ArithmeticFunction.mul_apply, Nat.floor_div_natCast, hfloor, hIcc, hdiv,
    natCoe_apply, hz1, hz2] at h
  simpa only [mul_comm] using h

open scoped Classical in
example {v : ArithmeticFunction ℂ} (hv : v.IsCompletelyMultiplicative)
    (w : ArithmeticFunction ℂ) (x : ℝ) :
    (∑ r ∈ Icc 1 ⌊x⌋₊, (w * (μ : ArithmeticFunction ℂ)) r *
      ∑ d ∈ r.divisors, (0 : ArithmeticFunction ℂ) d * v (r / d) *
        ∑ m ∈ d.divisors, (μ m : ℂ) * v m *
          ∑ j ∈ Icc 1 ⌊x / (m * r)⌋₊, (0 * v) j) = 0 := by
  have hz : (0 : ArithmeticFunction ℂ).IsCompletelyMultiplicative := by
    intro m n
    simp
  rw [← weighted_sum_dirichletConvolution_eq hz hv]
  simp

end MathlibExtTest.NumberTheory.WeightedDirichletConvolution
