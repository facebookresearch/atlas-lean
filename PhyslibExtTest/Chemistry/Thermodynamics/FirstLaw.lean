/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Thermodynamics.FirstLaw

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Tests for the first-law module

Exact checks: a reversible isothermal work instance with a computed numeric
value (both the closed form and the integral), an adiabatic invariant
instance, `Cp - Cv` instances (total and molar), a reversible/irreversible
work comparison instance, heat path dependence and energy path independence
instances, and boundary cases (equal volumes give zero work; an inadmissible
external pressure gives no comparison claim).
-/

@[expose] public section

open Chemistry.Thermodynamics

namespace PhyslibExtTest.Chemistry.Thermodynamics

-- Reversible isothermal work with a computed numeric value: `n = 2`, `R = 3`,
-- `T = 1`, `V₁ = 1`, `V₂ = e` gives `w = -6`.
example : isothermalWorkOn 2 3 1 1 (Real.exp 1) = -6 := by
  unfold isothermalWorkOn
  simp only [div_one, Real.log_exp]
  norm_num

-- The reversible isothermal integral agrees with the closed form numerically.
example : (∫ V in (1:ℝ)..Real.exp 1,
    -(idealGasP 2 3 1 V) ∂MeasureTheory.volume) = -6 := by
  rw [isothermal_work 2 3 1 1 (Real.exp 1) zero_lt_one (Real.exp_pos 1)]
  unfold isothermalWorkOn
  simp only [div_one, Real.log_exp]
  norm_num

-- Adiabatic invariant instance: `γ = 2`, `Cv = nR = 1`, states `(T₁, V₁) = (1, e)`
-- and `(T₂, V₂) = (e, 1)` satisfy `T₂ / T₁ = (V₁ / V₂) ^ (γ - 1)`.
example : (Real.exp 1 / 1 : ℝ) = (Real.exp 1 / 1) ^ ((2:ℝ) - 1) := by
  have had : (1:ℝ) * Real.log (Real.exp 1 / 1) + 1 * Real.log (1 / Real.exp 1)
      = 0 := by
    rw [div_one, one_div, Real.log_inv, Real.log_exp]
    norm_num
  have hγ : (2:ℝ) - 1 = 1 / 1 := by norm_num
  exact adiabatic_invariant_ratio_T 1 (Real.exp 1) (Real.exp 1) 1 1 1 2
    zero_lt_one (Real.exp_pos 1) (Real.exp_pos 1) zero_lt_one one_ne_zero hγ had

-- Adiabatic `p * V ^ γ` invariant instance with the same states and `n = R = 1`.
example : idealGasP 1 1 (Real.exp 1) 1 * (1:ℝ) ^ (2:ℝ)
    = idealGasP 1 1 1 (Real.exp 1) * (Real.exp 1) ^ (2:ℝ) := by
  have had : (1:ℝ) * Real.log (Real.exp 1 / 1) + 1 * Real.log (1 / Real.exp 1)
      = 0 := by
    rw [div_one, one_div, Real.log_inv, Real.log_exp]
    norm_num
  have hγ : (2:ℝ) - 1 = 1 / 1 := by norm_num
  exact adiabatic_invariant_pV 1 1 1 (Real.exp 1) (Real.exp 1) 1 1 1 2
    zero_lt_one zero_lt_one zero_lt_one (Real.exp_pos 1) (Real.exp_pos 1)
    zero_lt_one one_ne_zero hγ had

-- The `γ` chain: `γ = 5 / 3` with `Cp - Cv = nR` gives `γ - 1 = nR / Cv`.
example : ((5:ℝ) / 3) - 1 = 2 / 3 :=
  gamma_sub_one 5 3 2 (5 / 3) (by norm_num) rfl (by norm_num)

-- Total heat capacities: `Cp = 3 + 2`, `Cv = 3`, `nR = 2`.
example : (3:ℝ) + 2 - 3 = 2 := heatCapacity_linear 3 2 0

-- Molar heat capacities: `cp = 2 + 1`, `cv = 2`, `R = 1`.
example : (2:ℝ) + 1 - 2 = 1 := heatCapacity_linear 2 1 0

-- Reversible/irreversible comparison instance: `n = R = T = 1`, `V₁ = 1`,
-- `V₂ = 2`, `p_ext = 1 / 2 = p_final`.
example : |irreversibleWorkOn (1 / 2) 1 2|
    ≤ |isothermalWorkOn 1 1 1 1 2| :=
  irreversible_le_reversible 1 1 1 1 2 (1 / 2)
    zero_lt_one zero_lt_one zero_lt_one zero_lt_one (by norm_num) (by norm_num)
    (by norm_num)

-- Heat path dependence instance: `n = R = Cv = 1` on the rectangle
-- `[1, 2] × [1, 2]` gives different path integrals.
example : pathRightUp (heatCoeffV 1 1) (heatCoeffT 1)
      1 2 1 2
    ≠ pathUpRight (heatCoeffV 1 1) (heatCoeffT 1)
      1 2 1 2 :=
  heat_twoPaths_differ 1 1 1 1 2 1 2
    zero_lt_one zero_lt_one (by norm_num) zero_lt_one (by norm_num)

-- Energy path independence instance: `U = V + T` on `[1, 2] × [1, 2]`.
example : pathRightUp (fun _ _ : ℝ => 1) (fun _ _ : ℝ => 1) 1 2 1 2
    = pathUpRight (fun _ _ : ℝ => 1) (fun _ _ : ℝ => 1) 1 2 1 2 := by
  have hPderiv : ∀ T : ℝ, ∀ V ∈ Set.uIcc (1:ℝ) 2,
      HasDerivAt (fun V : ℝ => V + T) 1 V := by
    intro T V _
    have h := (hasDerivAt_id' V).add (hasDerivAt_const V T)
    rw [add_zero] at h
    exact h
  have hQderiv : ∀ V : ℝ, ∀ T ∈ Set.uIcc (1:ℝ) 2,
      HasDerivAt (fun T : ℝ => V + T) 1 T := by
    intro V T _
    have h := (hasDerivAt_const T V).add (hasDerivAt_id' T)
    rw [zero_add] at h
    exact h
  have hPint : ∀ T : ℝ,
      IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume 1 2 :=
    fun _ => intervalIntegrable_const
  have hQint : ∀ V : ℝ,
      IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume 1 2 :=
    fun _ => intervalIntegrable_const
  exact exact_twoPaths_equal (fun V T : ℝ => V + T) (fun _ _ : ℝ => 1)
    (fun _ _ : ℝ => 1) 1 2 1 2 hPderiv hPint hQderiv hQint

-- Boundary case: equal volumes give zero reversible isothermal work.
example (n R T V : ℝ) (hV : 0 < V) :
    isothermalWorkOn n R T V V = 0 := by
  unfold isothermalWorkOn
  rw [div_self (ne_of_gt hV), Real.log_one, mul_zero, neg_zero]

-- Boundary case: equal volumes give zero irreversible work.
example (p V : ℝ) : irreversibleWorkOn p V V = 0 := by
  unfold irreversibleWorkOn
  rw [sub_self, mul_zero, neg_zero]

-- Boundary case: an inadmissible external pressure (`p_ext = 10 > p_final`)
-- gives no comparison claim; here the inequality fails.
example : ¬ (|irreversibleWorkOn 10 1 2|
    ≤ |isothermalWorkOn 1 1 1 1 2|) := by
  have hL : |irreversibleWorkOn 10 1 2| = 10 := by
    unfold irreversibleWorkOn
    norm_num
  have hR : |isothermalWorkOn 1 1 1 1 2| = Real.log 2 := by
    unfold isothermalWorkOn
    simp only [div_one, one_mul, abs_neg]
    exact abs_of_nonneg (Real.log_nonneg (by norm_num))
  have h2pos : (0:ℝ) < 2 := by norm_num
  have hle1 := Real.log_le_sub_one_of_pos h2pos
  rw [hL, hR]
  intro hle
  linarith

end PhyslibExtTest.Chemistry.Thermodynamics
