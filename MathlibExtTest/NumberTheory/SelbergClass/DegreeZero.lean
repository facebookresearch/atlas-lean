/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.DegreeZero
public import MathlibExtTest.NumberTheory.SelbergClass.Basic

/-!
# Tests for degree-zero members of the Selberg class
-/

open Complex ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClassTest

theorem oneFE_degree : oneFE.degree = 0 := by
  unfold FunctionalEquation.degree
  rw [Finset.sum_eq_zero fun i _ => i.elim0, mul_zero]

example : (1 : ArithmeticFunction ℂ) = 1 :=
  eq_one_of_degree_eq_zero one_mem_selbergClass isLSeriesContinuation_one oneFE oneFE_degree

/-- `ζ` has no functional equation of degree `0`. -/
example (D : FunctionalEquation riemannZeta) : D.degree ≠ 0 := fun h =>
  zetaC_ne_one (eq_one_of_degree_eq_zero zeta_mem_selbergClass isLSeriesContinuation_zeta D h)

/-- `apply_eq_tsum_of_gammaFree_functionalEquation` at `a = 1`, `Q = 1`, `w = 1`, `n = 1`. -/
example : (1 : ArithmeticFunction ℂ) 1 = ∑' k : ℕ,
    if Real.log 1 + Real.log k - 2 * Real.log 1 = 0 then
      (if k = 0 then 0 else 1 * starRingEnd ℂ ((1 : ArithmeticFunction ℂ) k) *
        Complex.exp (((3 * Real.log 1 - Real.log 1 - 2 * Real.log k : ℝ) : ℂ))) else 0 := by
  have := apply_eq_tsum_of_gammaFree_functionalEquation 1 (fun _ => 1) (fun _ => 1) 0 0
    isLSeriesContinuation_one (fun _ hs => LSeriesSummable_of_mem one_mem_selbergClass
      (by linarith)) (differentiable_const _) (Complex.hasGrowthOrderLE_const _ _)
    (fun s _ => by simp) 1 one_pos 1 (by simp) (fun s _ _ => by simp) 1 one_ne_zero
  simpa using this

end SelbergClassTest
