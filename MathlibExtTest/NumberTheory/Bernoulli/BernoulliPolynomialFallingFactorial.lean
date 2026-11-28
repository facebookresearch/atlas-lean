/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.BernoulliPolynomialFallingFactorial
import Mathlib.Tactic.NormNum

/-! # Tests for the falling-factorial expansion of Bernoulli polynomials -/

open MathlibExt.NumberTheory.BernoulliSecondKindWanted

-- The interval of falling-factorial terms is empty at degree zero.
example : Polynomial.bernoulli 0 = 1 := by
  rw [bernoulli_poly_eq]
  simp

-- The constant term has the `B₁ = -1/2` convention.
example : Polynomial.bernoulli 1 = Polynomial.X - Polynomial.C (1 / 2 : ℚ) := by
  rw [bernoulli_poly_eq]
  simp [sub_eq_add_neg, div_eq_mul_inv, add_comm]

-- At `X = 2` the falling factorial of order three vanishes, leaving the order-two term.
example : (Polynomial.bernoulli 3).eval 2 = 3 := by
  have h₃ : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd ⟨1, rfl⟩ (by decide)
  rw [bernoulli_poly_eq, h₃]
  norm_num [Finset.sum_Icc_succ_top, descPochhammer_succ_right, Nat.stirlingSecond_succ_succ]
