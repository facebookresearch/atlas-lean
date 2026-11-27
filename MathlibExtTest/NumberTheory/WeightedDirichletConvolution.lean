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
formula, and boundary and small cases of the sum of a Dirichlet convolution over multiples.

Reference: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Theorem 1, Equation (8), and Lemma 3, Equation (20).
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

/-- The identity arithmetic function. -/
private def idFun : ArithmeticFunction ℂ := ⟨fun n : ℕ => (n : ℂ), by simp⟩

/-- The identity function is completely multiplicative. -/
private theorem idFun_cm : idFun.IsCompletelyMultiplicative := by
  intro m n
  simp only [idFun, ArithmeticFunction.coe_mk]
  exact Nat.cast_mul m n

-- Below the first positive integer, the divisor expansion vanishes for every `r`.
example (u v : ArithmeticFunction ℂ)
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative)
    (r : ℕ) {x : ℝ} (hx : x < 1) :
    (∑ d ∈ r.divisors, u d * v (r / d) * ∑ m ∈ d.divisors, (μ m : ℂ) * v m *
      ∑ j ∈ Finset.Icc 1 ⌊x / (m * r)⌋₊, (u * v) j) = 0 := by
  rw [← sum_dirichletConvolution_mul_eq hu hv]
  have hfloor : ⌊x / r⌋₊ = 0 := by
    rw [Nat.floor_eq_zero]
    by_cases hr : r = 0
    · simp [hr]
    · have hpos : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr
      by_cases hx0 : x ≤ 0
      · exact lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg hx0 hpos.le) zero_lt_one
      · push Not at hx0
        have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
        have hle : x / r ≤ x := by
          rw [div_le_iff₀ hpos]
          exact le_mul_of_one_le_right hx0.le hr1
        exact lt_of_le_of_lt hle hx
  simp [hfloor]

-- At `r = 2` and `x = 6` the expansion has two outer terms.
example (u v : ArithmeticFunction ℂ)
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative) :
    ∑ j ∈ Finset.Icc 1 3, (u * v) (2 * j) =
      u 1 * v 2 * (v 1 * ∑ j ∈ Finset.Icc 1 3, (u * v) j) +
      u 2 * v 1 * (v 1 * ∑ j ∈ Finset.Icc 1 3, (u * v) j +
        -1 * v 2 * ∑ j ∈ Finset.Icc 1 1, (u * v) j) := by
  have h := sum_dirichletConvolution_mul_eq hu hv 2 6
  have h62 : ⌊(6 : ℝ) / (2 : ℝ)⌋₊ = 3 := Nat.floor_div_eq_div 6 2
  have h622 : ⌊(6 : ℝ) / ((2 : ℝ) * (2 : ℝ))⌋₊ = 1 := by
    have e : (2 : ℝ) * (2 : ℝ) = (4 : ℝ) := by norm_num
    rw [e]
    exact Nat.floor_div_eq_div 6 4
  have hdiv2 : (2 : ℕ).divisors = {1, 2} := Nat.prime_two.divisors
  have h22 : (2 : ℕ) / 2 = 1 := by decide
  simpa [h62, h622, hdiv2, Nat.divisors_one, h22,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two] using h

-- For the identity function, both sides evaluate to `40` at `r = 2` and `x = 6`.
example : ∑ j ∈ Finset.Icc 1 3, (idFun * idFun) (2 * j) = 40 := by
  have h := sum_dirichletConvolution_mul_eq idFun_cm idFun_cm 2 6
  have h62 : ⌊(6 : ℝ) / (2 : ℝ)⌋₊ = 3 := Nat.floor_div_eq_div 6 2
  have h622 : ⌊(6 : ℝ) / ((2 : ℝ) * (2 : ℝ))⌋₊ = 1 := by
    have e : (2 : ℝ) * (2 : ℝ) = (4 : ℝ) := by norm_num
    rw [e]
    exact Nat.floor_div_eq_div 6 4
  have hdiv2 : (2 : ℕ).divisors = {1, 2} := Nat.prime_two.divisors
  have h22 : (2 : ℕ) / 2 = 1 := by decide
  have hexp : ∑ j ∈ Finset.Icc 1 3, (idFun * idFun) (2 * j) =
      idFun 1 * idFun 2 * (idFun 1 * ∑ j ∈ Finset.Icc 1 3, (idFun * idFun) j) +
      idFun 2 * idFun 1 * (idFun 1 * ∑ j ∈ Finset.Icc 1 3, (idFun * idFun) j +
        -1 * idFun 2 * ∑ j ∈ Finset.Icc 1 1, (idFun * idFun) j) := by
    simpa [h62, h622, hdiv2, Nat.divisors_one, h22,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two] using h
  have conv : ∀ n, (idFun * idFun) n = ∑ d ∈ n.divisors, idFun d * idFun (n / d) := by
    intro n
    rw [ArithmeticFunction.mul_apply]
    exact Nat.sum_divisorsAntidiagonal (fun a b => idFun a * idFun b)
  have e1 : (idFun * idFun) 1 = 1 := by
    rw [conv 1, Nat.divisors_one, Finset.sum_singleton]
    simp only [idFun, ArithmeticFunction.coe_mk]
    norm_num
  have e2 : (idFun * idFun) 2 = 4 := by
    rw [conv 2, hdiv2, Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)]
    simp only [idFun, ArithmeticFunction.coe_mk]
    norm_num
  have e3 : (idFun * idFun) 3 = 6 := by
    rw [conv 3, Nat.prime_three.divisors, Finset.sum_pair (by decide : (1 : ℕ) ≠ 3)]
    simp only [idFun, ArithmeticFunction.coe_mk]
    norm_num
  have f1 : idFun 1 = 1 := by simp [idFun]
  have f2 : idFun 2 = 2 := by simp [idFun]
  have hIcc3 : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  have hIcc1 : Finset.Icc 1 1 = ({1} : Finset ℕ) := by decide
  rw [hexp, f1, f2, hIcc3,
    Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3} : Finset ℕ) from by decide),
    Finset.sum_insert (show (2 : ℕ) ∉ ({3} : Finset ℕ) from by decide),
    Finset.sum_singleton, hIcc1, Finset.sum_singleton, e1, e2, e3]
  norm_num

end MathlibExtTest.NumberTheory.WeightedDirichletConvolution
