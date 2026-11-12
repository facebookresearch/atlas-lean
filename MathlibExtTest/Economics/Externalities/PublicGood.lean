/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Externalities.PublicGood
import Mathlib.Tactic

/-! Examples and checks for `MathlibExt.Economics.Externalities.PublicGood` (Atlas AP02.T02). -/

namespace MathlibExtTest.Economics.Externalities.PublicGood

open MathlibExt.Economics.PublicGood

/-- Test valuations: `v 0 G = 4 * G - G ^ 2`, `v 1 G = 2 * G`. -/
def testV : Fin 2 → ℝ → ℝ
  | 0 => fun G => 4 * G - G ^ 2
  | 1 => fun G => 2 * G

/-- Test cost: `cost G = G ^ 2`. -/
def testCost : ℝ → ℝ := fun G => G ^ 2

theorem testV_zero : testV 0 = fun G => 4 * G - G ^ 2 := rfl

theorem testV_one : testV 1 = fun G => 2 * G := rfl

/-- Surplus as a closed-form quadratic. -/
theorem surplus_eq (G : ℝ) : surplus testV testCost G = 6 * G - 2 * G ^ 2 := by
  have h0 : testV 0 G = 4 * G - G ^ 2 := congrFun testV_zero G
  have h1 : testV 1 G = 2 * G := congrFun testV_one G
  simp only [surplus, testCost, Fin.sum_univ_two, h0, h1]
  ring

/-- The interior optimum: surplus is globally maximized at `G = 3 / 2`. -/
theorem hopt : IsLocalMax (surplus testV testCost) (3 / 2) := by
  apply Filter.Eventually.of_forall
  intro x
  rw [surplus_eq x, surplus_eq (3 / 2)]
  nlinarith [sq_nonneg (x - 3 / 2)]

theorem hderiv_sq : HasDerivAt (fun G : ℝ => G ^ 2) 3 (3 / 2) := by
  have h := hasDerivAt_pow 2 (3 / 2 : ℝ)
  norm_num at h
  exact h

theorem hderiv_4G : HasDerivAt (fun G : ℝ => 4 * G) 4 (3 / 2) := by
  have h := HasDerivAt.const_mul (4 : ℝ) (hasDerivAt_id' (3 / 2 : ℝ))
  simpa using h

theorem hderiv_2G : HasDerivAt (fun G : ℝ => 2 * G) 2 (3 / 2) := by
  have h := HasDerivAt.const_mul (2 : ℝ) (hasDerivAt_id' (3 / 2 : ℝ))
  simpa using h

theorem hv0 : HasDerivAt (testV 0) 1 (3 / 2) := by
  rw [testV_zero]
  have h := hderiv_4G.sub hderiv_sq
  norm_num at h
  exact h

theorem hv1 : HasDerivAt (testV 1) 2 (3 / 2) := by
  rw [testV_one]
  exact hderiv_2G

theorem hc : HasDerivAt testCost 3 (3 / 2) := hderiv_sq

theorem hv : ∀ i, HasDerivAt (testV i) (![1, 2] i) (3 / 2) := by
  rw [Fin.forall_fin_two]
  constructor
  · simp only [Matrix.cons_val_zero]
    exact hv0
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    exact hv1

/-- Applying the Samuelson condition at the optimum. -/
example : ∑ i, ![1, 2] i = (3 : ℝ) :=
  sum_marginalBenefit_eq_marginalCost (v := testV) (cost := testCost) (G := 3 / 2)
    (mb := ![1, 2]) (mc := 3) hopt hv hc

end MathlibExtTest.Economics.Externalities.PublicGood
