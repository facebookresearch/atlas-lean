/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.Kinetics.ThermalInactivation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

/-!
# Tests for log-linear thermal inactivation

The rate at the reference temperature, the `z`-value as the temperature rise that multiplies the
rate by ten, the F-value of constant histories, and the decimal reduction they give: at a
constant temperature `T_ref` the reduction after time `t` is `t / D_ref`, the decimal reduction
time formula `D = t / (log₁₀ N₀ - log₁₀ N(t))`.
-/

open Real Set Chemistry.Kinetics.ThermalInactivation

namespace DomainsTest.Chemistry.Kinetics.ThermalInactivation

/-- At the reference temperature the rate is `ln 10 / D_ref`. -/
example (Dref Tref z : ℝ) : rate Dref Tref z Tref = Real.log 10 / Dref := by
  simp [rate]

/-- Raising the temperature by the `z`-value multiplies the rate by ten. -/
example (Dref Tref z θ : ℝ) (hz : z ≠ 0) :
    rate Dref Tref z (θ + z) = 10 * rate Dref Tref z θ := by
  have h : (θ + z - Tref) / z = 1 + (θ - Tref) / z := by field_simp; ring
  simp only [rate, h, rpow_add (by norm_num : (0 : ℝ) < 10), rpow_one]
  ring

/-- The F-value of a constant history at `T_ref + c z` after time `t` is `10 ^ c * t`. -/
example (Tref z c t : ℝ) (hz : z ≠ 0) :
    fValue Tref z (fun _ => Tref + c * z) t = 10 ^ c * t := by
  simp only [fValue, add_sub_cancel_left, mul_div_cancel_right₀ c hz]
  simp [mul_comm]

/-- The F-value vanishes at time zero. -/
example (Tref z : ℝ) (T : ℝ → ℝ) : fValue Tref z T 0 = 0 := by
  simp [fValue]

/-- At the constant temperature `T_ref` the decimal reduction after time `t` is `t / D_ref`. -/
example (Dref Tref z N₀ t : ℝ) (hN₀ : 0 < N₀) (ht : 0 ≤ t) :
    logb 10 (N₀ / (N₀ * exp (-∫ _ in (0 : ℝ)..t, rate Dref Tref z Tref))) = t / Dref := by
  have h := (log_linear_inactivation Dref Tref z (tf := t)
    (T := fun _ => Tref) continuousOn_const hN₀).2.2.2 t ⟨ht, le_rfl⟩
  simpa [fValue] using h

/-- One `z`-value above `T_ref` for one time unit, with `D_ref = 1`, reduces the
concentration ten-fold ten times: `log₁₀(N₀ / N(1)) = 10`. -/
example (Tref z N₀ : ℝ) (hz : z ≠ 0) (hN₀ : 0 < N₀) :
    logb 10 (N₀ / (N₀ * exp (-∫ _ in (0 : ℝ)..1, rate 1 Tref z (Tref + z)))) = 10 := by
  have h := (log_linear_inactivation 1 Tref z (tf := 1)
    (T := fun _ => Tref + z) continuousOn_const hN₀).2.2.2 1 ⟨zero_le_one, le_rfl⟩
  simpa [fValue, div_self hz] using h

/-- Uniqueness identifies the explicit exponential at a constant temperature: the solution at
`T_ref` is `N₀ e^{-(ln 10 / D_ref) t} = N₀ 10^{-t / D_ref}` on `[0, t_f]`. -/
example (Dref Tref z N₀ tf : ℝ) (hN₀ : 0 < N₀) :
    EqOn (fun t => N₀ * exp (-(Real.log 10 / Dref * t)))
      (fun t => N₀ * exp (-∫ _ in (0 : ℝ)..t, rate Dref Tref z Tref)) (Icc 0 tf) := by
  refine (log_linear_inactivation Dref Tref z (tf := tf)
    (T := fun _ => Tref) continuousOn_const hN₀).2.1 _ (by simp) fun t _ => ?_
  have hd : HasDerivAt (fun t => N₀ * exp (-(Real.log 10 / Dref * t)))
      (N₀ * (exp (-(Real.log 10 / Dref * t)) * -(Real.log 10 / Dref * 1))) t :=
    ((HasDerivAt.const_mul _ (hasDerivAt_id' t)).neg.exp).const_mul N₀
  convert hd.hasDerivWithinAt using 1
  simp only [rate, sub_self, zero_div, rpow_zero, mul_one]
  ring

/-- On the degenerate horizon `[0, 0]`, uniqueness only fixes the initial value. -/
example (Dref Tref z N₀ : ℝ) (T : ℝ → ℝ) (hN₀ : 0 < N₀) (M : ℝ → ℝ) (hM : M 0 = N₀) :
    M 0 = N₀ * exp (-∫ s in (0 : ℝ)..0, rate Dref Tref z (T s)) := by
  have hT : ContinuousOn T (Icc 0 0) := by
    simp only [Icc_self]
    exact continuousOn_singleton T 0
  refine (log_linear_inactivation Dref Tref z (tf := 0) hT hN₀).2.1 M hM (fun t ht => ?_)
    ⟨le_rfl, le_rfl⟩
  simp only [Icc_self, mem_singleton_iff] at ht ⊢
  subst ht
  exact HasFDerivWithinAt.of_not_accPt (by rw [accPt_principal_iff_nhdsWithin]; simp)

end DomainsTest.Chemistry.Kinetics.ThermalInactivation
