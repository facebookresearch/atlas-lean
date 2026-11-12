/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Welfare.DeadweightLoss

@[expose] public section

open scoped Topology
open Filter

namespace MathlibExtTest.Economics.Welfare.DeadweightLoss

open MathlibExt.Economics.DeadweightLoss


theorem taxEquilibrium_linear (τ : ℝ) :
    IsTaxEquilibrium (fun q => 10 - q) (fun q => q) τ ((10 - τ) / 2) := by
  show (10 - (10 - τ) / 2) - (10 - τ) / 2 = τ
  ring

theorem hasDerivAt_linear_antideriv (x : ℝ) :
    HasDerivAt (fun x => 10 * x - x ^ 2) ((10 * 1) - (2 * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => 10 * x) (10 * 1) x :=
    HasDerivAt.const_mul 10 (hasDerivAt_id x)
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa [Function.comp_def] using (hasDerivAt_pow 2 x).comp x (hasDerivAt_id x)
  exact h1.sub h2

theorem deadweightLoss_linear (τ : ℝ) :
    deadweightLoss (fun q => 10 - q) (fun q => q) 5 ((10 - τ) / 2) = τ ^ 2 / 4 := by
  have hFTC : (∫ x in ((10 - τ) / 2)..5, ((10 * 1) - (2 * x)))
      = (10 * 5 - 5 ^ 2) - (10 * ((10 - τ) / 2) - ((10 - τ) / 2) ^ 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_linear_antideriv x)
      ((by continuity : Continuous (fun x : ℝ => (10 * 1) - (2 * x))).intervalIntegrable _ _)
  have hfun : (fun x : ℝ => (10 - x) - x) = (fun x : ℝ => (10 * 1) - (2 * x)) := by
    ext x; ring
  show (∫ x in ((10 - τ) / 2)..5, ((10 - x) - x)) = τ ^ 2 / 4
  rw [hfun, hFTC]
  ring

theorem deriv_linear_demand : deriv (fun q : ℝ => 10 - q) 5 = -1 := by
  have h : deriv ((fun _ : ℝ => 10) - id) 5 = 0 - 1 :=
    ((hasDerivAt_const 5 10).sub (hasDerivAt_id 5)).deriv
  have h2 : deriv (fun q : ℝ => 10 - q) 5 = 0 - 1 := h
  rw [h2]
  norm_num

theorem deriv_linear_supply : deriv (fun q : ℝ => q) 5 = 1 :=
  (hasDerivAt_id 5).deriv

example (τ : ℝ) : deadweightLoss (fun q => 10 - q) (fun q => q) 5 ((10 - τ) / 2)
    = τ ^ 2 / (2 * (deriv (fun q => q) 5 - deriv (fun q => 10 - q) 5)) := by
  rw [deadweightLoss_linear, deriv_linear_supply, deriv_linear_demand]
  norm_num

theorem hasDerivAt_nonlinear_antideriv (x : ℝ) :
    HasDerivAt (fun x => (8 * x - x ^ 2) - (1 / 3) * (x ^ 3))
      (((8 * 1) - (2 * x)) - ((1 / 3) * (3 * x ^ 2))) x := by
  have h1 : HasDerivAt (fun x : ℝ => 8 * x - x ^ 2) ((8 * 1) - (2 * x)) x := by
    have ha : HasDerivAt (fun x : ℝ => 8 * x) (8 * 1) x :=
      HasDerivAt.const_mul 8 (hasDerivAt_id x)
    have hb : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      simpa [Function.comp_def] using (hasDerivAt_pow 2 x).comp x (hasDerivAt_id x)
    exact ha.sub hb
  have h2 : HasDerivAt (fun x : ℝ => (1 / 3) * (x ^ 3)) ((1 / 3) * (3 * x ^ 2)) x := by
    have hc : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by
      simpa [Function.comp_def] using (hasDerivAt_pow 3 x).comp x (hasDerivAt_id x)
    exact hc.const_mul (1 / 3)
  exact h1.sub h2

theorem deadweightLoss_nonlinear :
    deadweightLoss (fun q => 8 - 2 * q) (fun q => q ^ 2) 2 1 = 8 / 3 := by
  have hFTC : (∫ x in (1:ℝ)..2, (((8 * 1) - (2 * x)) - ((1 / 3) * (3 * x ^ 2))))
      = ((8 * 2 - 2 ^ 2) - (1 / 3) * (2 ^ 3)) - ((8 * 1 - 1 ^ 2) - (1 / 3) * (1 ^ 3)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_nonlinear_antideriv x)
      ((by continuity : Continuous
        (fun x : ℝ => ((8 * 1) - (2 * x)) - ((1 / 3) * (3 * x ^ 2)))).intervalIntegrable _ _)
  have hfun : (fun x : ℝ => (8 - 2 * x) - x ^ 2)
      = (fun x : ℝ => ((8 * 1) - (2 * x)) - ((1 / 3) * (3 * x ^ 2))) := by
    ext x; ring
  show (∫ x in (1:ℝ)..2, ((8 - 2 * x) - x ^ 2)) = 8 / 3
  rw [hfun, hFTC]
  norm_num

example : IsTaxEquilibrium (fun q => 8 - 2 * q) (fun q => q ^ 2) 5 1 := by
  show (8 - 2 * 1) - 1 ^ 2 = 5
  norm_num

theorem deriv_nonlinear_supply : deriv (fun q : ℝ => q ^ 2) 2 = 4 := by
  have hgen : ∀ y : ℝ, HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := fun y => by
    simpa [Function.comp_def] using (hasDerivAt_pow 2 y).comp y (hasDerivAt_id y)
  have hder := (hgen 2).deriv
  rw [hder]
  norm_num

theorem deriv_nonlinear_demand : deriv (fun q : ℝ => 8 - 2 * q) 2 = -2 := by
  have h : HasDerivAt (fun q : ℝ => 8 - 2 * q) (0 - (2 * 1)) 2 :=
    (hasDerivAt_const 2 8).sub (HasDerivAt.const_mul 2 (hasDerivAt_id 2))
  have hder := h.deriv
  rw [hder]
  norm_num

example : deadweightLoss (fun q => 8 - 2 * q) (fun q => q ^ 2) 2 1
    ≠ (5 ^ 2) / (2 * (deriv (fun q => q ^ 2) 2 - deriv (fun q => 8 - 2 * q) 2)) := by
  rw [deadweightLoss_nonlinear, deriv_nonlinear_supply, deriv_nonlinear_demand]
  norm_num

example : (fun τ : ℝ => deadweightLoss (fun q => 10 - q) (fun q => q) 5
      ((10 - τ) / 2) - τ ^ 2 / (2 * (deriv (fun q => q) 5
        - deriv (fun q => 10 - q) 5)))
    =O[𝓝 (0 : ℝ)] fun τ : ℝ => τ ^ 3 := by
  have hd : ContDiffAt ℝ 2 (fun q : ℝ => 10 - q) 5 :=
    (contDiff_const.sub contDiff_id).contDiffAt
  have hs : ContDiffAt ℝ 2 (fun q : ℝ => q) 5 := contDiff_id.contDiffAt
  have d1 : deriv (fun q : ℝ => q) 5 = 1 := deriv_linear_supply
  have d2 : deriv (fun q : ℝ => 10 - q) 5 = -1 := deriv_linear_demand
  have hslope : (0 : ℝ) < deriv (fun q => q) 5 - deriv (fun q => 10 - q) 5 := by
    rw [d1, d2]; norm_num
  have hq0 : (fun τ : ℝ => (10 - τ) / 2) 0 = 5 := by
    show (10 - 0) / 2 = 5; norm_num
  have hqc : ContinuousAt (fun τ : ℝ => (10 - τ) / 2) 0 :=
    (continuousAt_const.sub continuousAt_id).div_const 2
  have hqeq : ∀ᶠ τ in 𝓝 (0 : ℝ), IsTaxEquilibrium (fun q => 10 - q) (fun q => q)
      τ ((10 - τ) / 2) :=
    Filter.Eventually.of_forall taxEquilibrium_linear
  exact deadweightLoss_sub_harberger_isBigO hd hs hslope hq0 hqc hqeq

end MathlibExtTest.Economics.Welfare.DeadweightLoss
