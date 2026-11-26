/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.ComplementaryPolynomials
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for complementary polynomials on the unit circle -/

open Polynomial
open scoped Polynomial

namespace MathlibExtTest.Analysis.ComplementaryPolynomials

open MathlibExt.Analysis.ComplementaryPolynomialsWanted.ComplexAnalysis

-- The complement of the coordinate monomial must vanish everywhere on the circle.
example : ∃ Q : ℂ[X], Q.natDegree ≤ 1 ∧ ∀ z : Circle, Q.eval (z : ℂ) = 0 := by
  obtain ⟨Q, hQ, h⟩ := exists_complementary_polynomial_on_unit_circle
    (X : ℂ[X]) (hP := fun z => by simp)
  refine ⟨Q, by simpa using hQ, fun z => ?_⟩
  have hz := h z
  simp only [eval_X, Circle.norm_coe, one_pow] at hz
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (Q.eval (z : ℂ))])

-- A scaled monomial has a positive constant gap, despite having degree two.
example : ∃ Q : ℂ[X], Q.natDegree ≤ 2 ∧ ∀ z : Circle, ‖Q.eval (z : ℂ)‖ ^ 2 = 3 / 4 := by
  let P : ℂ[X] := C (1 / 2) * X ^ 2
  have hnorm (z : Circle) : ‖P.eval (z : ℂ)‖ = 1 / 2 := by
    simp [P, norm_pow]
  obtain ⟨Q, hQ, h⟩ := exists_complementary_polynomial_on_unit_circle P
    (fun z => by rw [hnorm]; norm_num)
  refine ⟨Q, hQ.trans (natDegree_mul_le.trans (by simp)), fun z => ?_⟩
  have hz := h z
  rw [hnorm] at hz
  linarith

-- The complement vanishes at the saturation point, and has norm one at its antipode.
example : ∃ Q : ℂ[X], Q.natDegree ≤ 1 ∧ Q.eval 1 = 0 ∧ ‖Q.eval (-1)‖ = 1 := by
  let P : ℂ[X] := C (1 / 2) * (1 + X)
  have hP (z : Circle) : ‖P.eval (z : ℂ)‖ ≤ 1 := by
    have hz := norm_add_le (1 : ℂ) (z : ℂ)
    rw [norm_one, Circle.norm_coe] at hz
    simp [P]
    linarith
  obtain ⟨Q, hQ, h⟩ := exists_complementary_polynomial_on_unit_circle P hP
  refine ⟨Q, hQ.trans (natDegree_mul_le.trans (by simp)), ?_, ?_⟩
  · have hz := h (1 : Circle)
    have hp : P.eval 1 = 1 := by norm_num [P]
    rw [Circle.coe_one, hp, norm_one, one_pow] at hz
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (Q.eval 1)])
  · have hz := h (-1 : Circle)
    have hp : P.eval (-1) = 0 := by norm_num [P]
    rw [Circle.coe_neg, Circle.coe_one, hp, norm_zero, zero_pow (by decide), zero_add] at hz
    nlinarith [norm_nonneg (Q.eval (-1))]

end MathlibExtTest.Analysis.ComplementaryPolynomials
