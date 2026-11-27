/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Economics.Actuarial.Thiele
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Tests for the deterministic two-state reserve -/

open Domains.Economics.Actuarial Set

-- A premium of three for two years with no interest or exits gives an initial reserve of −6.
-- The ordinary derivative is +3 even when the premium is arbitrary outside the policy interval.
example {p : ℝ → ℝ} (hp : EqOn p (fun _ => 3) (Icc 0 2)) :
    let V := twoStateReserve (fun _ => 0) (fun _ => 0) p (fun _ => 4) 2 0
    V 0 = -6 ∧ ∀ t ∈ Ioo 0 2, HasDerivAt V 3 t := by
  constructor
  · simp only [twoStateReserve, intervalIntegral.integral_zero, neg_zero, Real.exp_zero,
      zero_mul, zero_sub, one_mul, mul_zero, add_zero]
    calc
      (∫ s in (0 : ℝ)..2, -p s) = ∫ _ in (0 : ℝ)..2, (-3 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hs
        exact congrArg Neg.neg (hp hs)
      _ = -6 := by norm_num [intervalIntegral.integral_const]
  · intro t ht
    have hd := (thiele_differentialEquation (δ := fun _ => 0) (μ := fun _ => 0)
      (π := p) (b := fun _ => 4) (T := 2) 0 (by norm_num) continuousOn_const continuousOn_const
      (continuousOn_const.congr hp) continuousOn_const).2 t ht
    simpa [hp (Ioo_subset_Icc_self ht)] using hd

private noncomputable abbrev policy :=
  twoStateReserve (fun _ => 0) (fun s => s) (fun s => 1 + 2 * s - s ^ 2) (fun _ => 3) 1 2

-- Evaluate the reserve integral independently of the differential equation: for fixed t the
-- antiderivative of the weighted net costs is −(1+s) exp(−(s²−t²)/2).
private theorem policy_value (t : ℝ) : policy t = 1 + t := by
  let K := fun s : ℝ => Real.exp (-((s ^ 2 - t ^ 2) / 2))
  have dK (s : ℝ) : HasDerivAt K (K s * (-s)) s := by
    apply HasDerivAt.congr_deriv ((((hasDerivAt_id s).pow 2).sub_const (t ^ 2)).div_const 2).neg.exp
    dsimp [K]
    ring
  have dcost (s : ℝ) : HasDerivAt (fun u => -(1 + u) * K u)
      (K s * (s * 3 - (1 + 2 * s - s ^ 2))) s := by
    apply HasDerivAt.congr_deriv (((hasDerivAt_id s).const_add 1).neg.mul (dK s))
    dsimp
    ring
  simp only [policy, twoStateReserve, zero_add, integral_id]
  change (∫ s in t..1, K s * (s * 3 - (1 + 2 * s - s ^ 2))) + K 1 * 2 = 1 + t
  have hcont : Continuous (fun s => K s * (s * 3 - (1 + 2 * s - s ^ 2))) := by
    dsimp [K]
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => dcost s)
    (hcont.intervalIntegrable _ _)]
  have hK : K t = 1 := by simp [K]
  rw [hK]
  ring

-- The API gives a nonzero maturity benefit and an ordinary derivative for the actual reserve.
example : policy 1 = 2 ∧ ∀ t ∈ Ioo 0 1, HasDerivAt policy 1 t := by
  obtain ⟨hterm, hderiv⟩ := thiele_differentialEquation (δ := fun _ => 0) (μ := fun s => s)
    (π := fun s => 1 + 2 * s - s ^ 2) (b := fun _ => 3) (T := 1) 2 (by norm_num)
    continuousOn_const continuousOn_id (by fun_prop) continuousOn_const
  refine ⟨hterm, fun t ht => (hderiv t ht).congr_deriv ?_⟩
  change (0 + t) * policy t + (1 + 2 * t - t ^ 2) - t * 3 = 1
  rw [policy_value]
  ring
