/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.EnestromKakeya
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Analysis.Complex.EnestromKakeya`

Examples for the monotone form of the Eneström–Kakeya theorem,
`MetaMathlibExt.norm_le_one_of_aeval_eq_zero_of_monotone_coeff`.
-/

namespace MathlibExtTest.Analysis.Complex.EnestromKakeya

open Polynomial MetaMathlibExt

-- Equal coefficients `1 ≤ 1 ≤ 1`: every root of `1 + X + X²` lies in the closed unit disc.
example (z : ℂ) (hz : aeval z (1 + X + X ^ 2 : ℝ[X]) = 0) : ‖z‖ ≤ 1 := by
  have hdeg : (1 + X + X ^ 2 : ℝ[X]).natDegree = 2 := by compute_degree!
  refine norm_le_one_of_aeval_eq_zero_of_monotone_coeff _ ?_ ?_ ?_ z hz
  · rintro h
    simp [h] at hdeg
  · simp
  · rw [hdeg]
    intro i hi
    interval_cases i <;> simp [coeff_one, coeff_X]

-- A zero constant term is allowed, `0 ≤ 1 ≤ 2 ≤ 3`: every root of `X + 2 X² + 3 X³` lies in the
-- closed unit disc.
example (z : ℂ) (hz : aeval z (X + C 2 * X ^ 2 + C 3 * X ^ 3 : ℝ[X]) = 0) : ‖z‖ ≤ 1 := by
  have hdeg : (X + C 2 * X ^ 2 + C 3 * X ^ 3 : ℝ[X]).natDegree = 3 := by compute_degree!
  refine norm_le_one_of_aeval_eq_zero_of_monotone_coeff _ ?_ ?_ ?_ z hz
  · rintro h
    simp [h] at hdeg
  · simp
  · rw [hdeg]
    intro i hi
    interval_cases i <;> norm_num [coeff_X, coeff_C_mul_X_pow]

-- The bound is attained, so the hypotheses are satisfiable: `1 + X` meets all of them and has
-- the root `-1`, of norm `1`.
example : ∃ p : ℝ[X], p ≠ 0 ∧ 0 ≤ p.coeff 0 ∧
    (∀ i < p.natDegree, p.coeff i ≤ p.coeff (i + 1)) ∧ ∃ z : ℂ, aeval z p = 0 ∧ ‖z‖ = 1 := by
  have hdeg : (1 + X : ℝ[X]).natDegree = 1 := by compute_degree!
  refine ⟨1 + X, ?_, by simp, ?_, -1, by simp, by simp⟩
  · rintro h
    simp [h] at hdeg
  · rw [hdeg]
    intro i hi
    interval_cases i
    simp [coeff_one]

-- The hypothesis `0 ≤ a₀` cannot be dropped: `X² + X - 6 = (X + 3) (X - 2)` is nonzero with
-- monotone coefficients `-6 ≤ 1 ≤ 1`, and its root `-3` has norm `3`.
example : ∃ p : ℝ[X], p ≠ 0 ∧ (∀ i < p.natDegree, p.coeff i ≤ p.coeff (i + 1)) ∧
    ∃ z : ℂ, aeval z p = 0 ∧ 1 < ‖z‖ := by
  have hdeg : (X ^ 2 + X - C 6 : ℝ[X]).natDegree = 2 := by compute_degree!
  refine ⟨X ^ 2 + X - C 6, ?_, ?_, -3, ?_, ?_⟩
  · rintro h
    simp [h] at hdeg
  · rw [hdeg]
    intro i hi
    interval_cases i <;> norm_num [coeff_X, coeff_X_pow, coeff_C]
  · simp
    norm_num
  · simp

-- Monotonicity cannot be dropped: `2 + X` is nonzero with `0 ≤ 2` but decreasing coefficients
-- `2 > 1`, and its root `-2` has norm `2`.
example : ∃ p : ℝ[X], p ≠ 0 ∧ 0 ≤ p.coeff 0 ∧ ∃ z : ℂ, aeval z p = 0 ∧ 1 < ‖z‖ := by
  refine ⟨C 2 + X, ?_, by simp, -2, ?_, ?_⟩
  · intro h
    simpa using congrArg (·.coeff 1) h
  · simp
  · simp

end MathlibExtTest.Analysis.Complex.EnestromKakeya
