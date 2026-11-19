/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.IntertemporalChoice.ConsumptionSmoothing
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for consumption smoothing

Log utility: the Euler equation at `β = 1/2`, `r = 1` with `c₀ = 3` forces `c₁ = 3`.
Quadratic utility `u c = 4 c - c²`, `β = 1/2`, `r = 1`, `y₀ = 2`, `y₁ = 0`: the maximizer
`c₀ = 4/3` is proved, and the theorem gives `c₁ = 4/3`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.IntertemporalChoice.ConsumptionSmoothing

open MathlibExt.Economics.IntertemporalChoice

-- Test 1: log utility, `u = Real.log`.
example (c₁ : ℝ) (hc₁ : 0 < c₁)
    (heuler : deriv Real.log 3 = (1 / 2) * (1 + 1) * deriv Real.log c₁) :
    c₁ = 3 := by
  have hmu : StrictAntiOn (deriv Real.log) (Set.Ioi 0) := by
    intro x hx y hy hxy
    rw [Real.deriv_log, Real.deriv_log]
    exact inv_strictAntiOn hx hy hxy
  have h : (3 : ℝ) = c₁ :=
    eq_of_euler_of_discount_mul_gross_eq_one (u := Real.log) (β := 1 / 2) (r := 1)
      heuler (by norm_num) hmu (by norm_num) hc₁
  exact h.symm

-- Test 2: quadratic utility `u c = 4 * c - c ^ 2`, `β = 1/2`, `r = 1`, `y₀ = 2`, `y₁ = 0`.
private theorem quad_hderiv_eq : ∀ x : ℝ, deriv (fun c : ℝ => 4 * c - c ^ 2) x = 4 - 2 * x := by
  intro x
  have h1 : HasDerivAt (fun c : ℝ => 4 * c) 4 x := by
    simpa using (hasDerivAt_id x).const_mul (4 : ℝ)
  have h2 : HasDerivAt (fun c : ℝ => c ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h : HasDerivAt (fun c : ℝ => 4 * c - c ^ 2) (4 - 2 * x) x := h1.sub h2
  exact HasDerivAt.deriv h

private theorem quad_hmu : StrictAntiOn (deriv (fun c : ℝ => 4 * c - c ^ 2)) (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [quad_hderiv_eq a, quad_hderiv_eq b]
  linarith

private theorem quad_hu : ∀ x : ℝ, DifferentiableAt ℝ (fun c : ℝ => 4 * c - c ^ 2) x := by
  intro x
  fun_prop

private theorem quad_isMaxOn : IsMaxOn
    (lifetimeUtility (fun c : ℝ => 4 * c - c ^ 2) (1 / 2) 1 2 0)
    (feasibleConsumption 1 2 0) (4 / 3) := by
  intro c hc
  simp only [lifetimeUtility, secondPeriodConsumption, feasibleConsumption, Set.mem_ofPred] at hc ⊢
  nlinarith [sq_nonneg (c - 4 / 3), hc.1, hc.2]

example : IsMaxOn
    (lifetimeUtility (fun c : ℝ => 4 * c - c ^ 2) (1 / 2) 1 2 0)
    (feasibleConsumption 1 2 0) (4 / 3) :=
  quad_isMaxOn

example : (4 : ℝ) / 3 = secondPeriodConsumption 1 2 0 (4 / 3) := by
  have hmax := quad_isMaxOn
  have hc₀ : (0 : ℝ) < 4 / 3 := by norm_num
  have hc₁ : (0 : ℝ) < secondPeriodConsumption 1 2 0 (4 / 3) := by
    unfold secondPeriodConsumption
    norm_num
  have hu₀ := quad_hu (4 / 3)
  have hu₁ := quad_hu (secondPeriodConsumption 1 2 0 (4 / 3))
  have hβr : (1 / 2 : ℝ) * (1 + 1) = 1 := by norm_num
  exact consumption_eq_of_discount_mul_gross_eq_one (u := fun c : ℝ => 4 * c - c ^ 2)
    (β := 1 / 2) (r := 1) (y₀ := 2) (y₁ := 0) (c₀ := 4 / 3)
    hmax hc₀ hc₁ hu₀ hu₁ hβr quad_hmu

example : secondPeriodConsumption (1 : ℝ) 2 0 (4 / 3) = 4 / 3 := by
  unfold secondPeriodConsumption
  norm_num

end MathlibExtTest.Economics.IntertemporalChoice.ConsumptionSmoothing
