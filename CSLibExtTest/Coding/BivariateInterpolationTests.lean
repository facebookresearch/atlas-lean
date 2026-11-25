/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.BivariateInterpolation
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range

@[expose] public section

namespace Cslib.CodingTheory.BivariateInterpolationTests

open Polynomial Finset

/-- Weighted monomial counts at `w = 1, D = 2` and `w = 0, D = 2`. -/
example : (((range 3 ×ˢ range 3).filter
    fun ij : ℕ × ℕ => ij.1 + 1 * ij.2 ≤ 2).card) = 6 := by
  decide

example : (((range 3 ×ˢ range 3).filter
    fun ij : ℕ × ℕ => ij.1 + 0 * ij.2 ≤ 2).card) = 9 := by
  decide

/-- The `k = 1` case is nonvacuous: `X * (X - 1)` over `ℚ`. -/
example :
    let Q : ℚ[X][X] := C (X * (X - 1))
    let α : Fin 2 → ℚ := ![0, 1]
    let y : Fin 2 → ℚ := ![0, 1]
    Q ≠ 0 ∧
      Cslib.CodingTheory.GuruswamiSudan.WeightedDegLE 0 2 Q ∧
      ∀ i, (Q.eval (C (y i))).eval (α i) = 0 := by
  intro Q α y
  have hQ : Q = C (X * (X - 1) : ℚ[X]) := rfl
  have hα : α = (![0, 1] : Fin 2 → ℚ) := rfl
  have hy : y = (![0, 1] : Fin 2 → ℚ) := rfl
  have hX : (X : ℚ[X]) ≠ 0 := Polynomial.X_ne_zero
  have hX1 : (X - 1 : ℚ[X]) ≠ 0 := by
    have hdeg : (X - 1 : ℚ[X]).natDegree = 1 := by
      rw [← Polynomial.C_1, Polynomial.natDegree_X_sub_C]
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have hprod : (X * (X - 1) : ℚ[X]) ≠ 0 := mul_ne_zero hX hX1
  refine ⟨?_, ?_, ?_⟩
  · rw [hQ]
    exact Polynomial.C_ne_zero.mpr hprod
  · unfold Cslib.CodingTheory.GuruswamiSudan.WeightedDegLE
    intro j i hij
    rw [hQ] at hij
    by_cases hj : j = 0
    · subst hj
      rw [Polynomial.coeff_C_zero] at hij
      have hdeg : (X * (X - 1) : ℚ[X]).natDegree = 2 := by
        have h1 : (X - 1 : ℚ[X]).natDegree = 1 := by
          rw [← Polynomial.C_1, Polynomial.natDegree_X_sub_C]
        rw [Polynomial.natDegree_mul hX hX1, Polynomial.natDegree_X, h1]
      have hle : i ≤ (X * (X - 1) : ℚ[X]).natDegree :=
        Polynomial.le_natDegree_of_ne_zero hij
      omega
    · rw [Polynomial.coeff_C_of_ne_zero hj, Polynomial.coeff_zero] at hij
      simp at hij
  · rw [Fin.forall_fin_two, hy, hα]
    constructor
    · simp only [Matrix.cons_val_zero, hQ, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_one, zero_mul]
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, hQ,
        Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_one, sub_self, mul_zero]

#check @Cslib.CodingTheory.BivariateInterpolation.hasRootMult_one_iff
#check @Cslib.CodingTheory.BivariateInterpolation.card_weighted_monomials_ge
#check @Cslib.CodingTheory.BivariateInterpolation.two_mul_card_weighted_monomials_ge
#check @Cslib.CodingTheory.BivariateInterpolation.exists_bivariate_interpolant
#check @Cslib.CodingTheory.BivariateInterpolation.exists_bivariate_interpolant_sqrt
#check @Cslib.CodingTheory.BivariateInterpolation.exists_bivariate_interpolant_mvPolynomial

#print axioms Cslib.CodingTheory.BivariateInterpolation.hasRootMult_one_iff
#print axioms Cslib.CodingTheory.BivariateInterpolation.card_weighted_monomials_ge
#print axioms Cslib.CodingTheory.BivariateInterpolation.two_mul_card_weighted_monomials_ge
#print axioms Cslib.CodingTheory.BivariateInterpolation.exists_bivariate_interpolant
#print axioms Cslib.CodingTheory.BivariateInterpolation.exists_bivariate_interpolant_sqrt
#print axioms Cslib.CodingTheory.BivariateInterpolation.exists_bivariate_interpolant_mvPolynomial

theorem ceilSqrt_zero : Cslib.CodingTheory.BivariateInterpolation.ceilSqrt 0 = 0 := by
  decide

theorem ceilSqrt_four : Cslib.CodingTheory.BivariateInterpolation.ceilSqrt 4 = 2 := by
  unfold Cslib.CodingTheory.BivariateInterpolation.ceilSqrt
  have h4 : Nat.sqrt 4 = 2 := Nat.sqrt_eq 2
  rw [h4]
  decide

theorem ceilSqrt_three : Cslib.CodingTheory.BivariateInterpolation.ceilSqrt 3 = 2 := by
  unfold Cslib.CodingTheory.BivariateInterpolation.ceilSqrt
  have h3 : Nat.sqrt 3 = 1 := by
    rw [eq_comm]
    exact Nat.eq_sqrt.mpr ⟨by decide, by decide⟩
  rw [h3]
  decide

end Cslib.CodingTheory.BivariateInterpolationTests
