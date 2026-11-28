/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Polynomial.Roots
import MathlibExt.NumberTheory.Bernoulli.BernoulliSecondKindStirlingSum
import MathlibExt.NumberTheory.Bernoulli.FallingFactorialBernoulliPolynomial

/-! # Tests for falling factorials in the Bernoulli polynomial basis -/

open Finset MetaMathlibExt MathlibExt.NumberTheory.BernoulliSecondKindWanted
open Polynomial (C)

-- Check directly that the empty sum leaves the constant polynomial 1.
example : descPochhammer ℚ 0 = C (bernoulliSecond 0) +
    ∑ k ∈ Icc 1 0, C ((0 : ℚ) / k * (signedStirlingFirst (0 - 1) (k - 1) : ℚ)) *
      Polynomial.bernoulli k := by
  simp [bernoulliSecond_eq_sum]

-- Check the whole cubic independently at all rational inputs. The term for `k = 1`
-- vanishes, the term for `k = 2` is negative, and the term for `k = 3` is monic.
example : descPochhammer ℚ 3 = C (bernoulliSecond 3) +
    ∑ k ∈ Icc 1 3, C ((3 : ℚ) / k * (signedStirlingFirst (3 - 1) (k - 1) : ℚ)) *
      Polynomial.bernoulli k := by
  have h₁ : bernoulli 1 = -1 / 2 := bernoulli_one
  have h₂ : bernoulli 2 = 1 / 6 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : (2 : ℕ) ≠ 1), bernoulli'_two]
  have h₃ : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd ⟨1, rfl⟩ (by decide)
  have hB : bernoulliSecond 3 = 1 / 4 := by
    rw [bernoulliSecond_eq_sum]
    norm_num [Finset.sum_range_succ, signedStirlingFirst_succ_succ]
  apply Polynomial.funext
  intro x
  norm_num [descPochhammer_succ_eval, Finset.sum_Icc_succ_top, hB,
    signedStirlingFirst_succ_succ, Polynomial.eval_finsetSum, Polynomial.bernoulli_def,
    Finset.sum_range_succ, h₁, h₂, h₃]
  ring

-- A client can use the public theorem at a concrete order.
example : descPochhammer ℚ 2 = C (bernoulliSecond 2) +
    ∑ k ∈ Icc 1 2, C ((2 : ℚ) / k * (signedStirlingFirst (2 - 1) (k - 1) : ℚ)) *
      Polynomial.bernoulli k :=
  descPochhammer_eq 2
