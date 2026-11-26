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
# Tests for sums of a Dirichlet convolution over multiples
-/

namespace MathlibExtTest.NumberTheory.WeightedDirichletConvolution

open ArithmeticFunction Finset MetaMathlibExt
open scoped ArithmeticFunction.Moebius

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
  have e4 : (idFun * idFun) 4 = 12 := by
    rw [conv 4, show (4 : ℕ).divisors = {1, 2, 4} from by decide,
      Finset.sum_insert (show (1 : ℕ) ∉ ({2, 4} : Finset ℕ) from by decide),
      Finset.sum_insert (show (2 : ℕ) ∉ ({4} : Finset ℕ) from by decide),
      Finset.sum_singleton]
    simp only [idFun, ArithmeticFunction.coe_mk]
    norm_num
  have e6 : (idFun * idFun) 6 = 24 := by
    rw [conv 6, show (6 : ℕ).divisors = {1, 2, 3, 6} from by decide,
      Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3, 6} : Finset ℕ) from by decide),
      Finset.sum_insert (show (2 : ℕ) ∉ ({3, 6} : Finset ℕ) from by decide),
      Finset.sum_insert (show (3 : ℕ) ∉ ({6} : Finset ℕ) from by decide),
      Finset.sum_singleton]
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
