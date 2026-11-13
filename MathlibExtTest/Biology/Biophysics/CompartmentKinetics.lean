/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.CompartmentKinetics

/-! Tests for one-compartment linear pharmacokinetics: concrete clearance, volume, AUC and
half-life values, derivatives at sample parameters, a non-vacuity witness for `IsSolution`, and
the three boundary regimes. -/

open Real Filter Topology

namespace MathlibExtTest.Biology.Biophysics.CompartmentKinetics

open MathlibExt.Biology.Biophysics.CompartmentKinetics

/-- `CL = 2`, `V = 10`: `k = 1/5`. -/
example : elimRate 2 10 = 1 / 5 := by norm_num [elimRate]

/-- `CL = 2`, `V = 10`: `t½ = 5 log 2`. -/
example : halfLife (elimRate 2 10) = 5 * log 2 := by
  rw [halfLife_elimRate]; ring

/-- Non-vacuity: the explicit amount is a solution, with the prescribed initial amount. -/
example : IsSolution (1 / 5) 3 (amount (1 / 5) 3 100) := isSolution_amount _ _ _

example : amount (1 / 5) 3 100 0 = 100 := amount_zero _ _ _

/-- Derivative at sample parameters `k = 1`, `R = 2`, `A₀ = 3`, `t = 0`: `A'(0) = 2 - 3 = -1`. -/
example : HasDerivAt (amount 1 2 3) (-1) 0 := by
  convert hasDerivAt_amount 1 2 3 0 using 1
  norm_num

/-- `A₀ = A∞` is an equilibrium: `k = 1/2`, `R = 1`, `A₀ = 2` stays at `2`. -/
example (t : ℝ) : amount (1 / 2) 1 2 t = 2 := by
  rw [amount_eq_of_ne_zero (by norm_num)]; norm_num

/-- Explicit formula at `k = 1`, `R = 2`, `A₀ = 0`, `t = log 2`: `A = 2 (1 - 1/2) = 1`. -/
example : amount 1 2 0 (log 2) = 1 := by
  rw [amount_eq_of_ne_zero one_ne_zero, show -1 * log 2 = -log 2 by ring, exp_neg,
    exp_log two_pos]
  norm_num

/-- `k = 0`: linear accumulation, `A(3) = 1 + 2·3 = 7`. -/
example : amount 0 2 1 3 = 7 := by rw [amount_rate_zero]; norm_num

/-- Nonnegativity for sample nonnegative parameters. -/
example : 0 ≤ amount (1 / 5) 3 100 7 :=
  amount_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Mass balance at `k = 1`, `R = 2`, `A₀ = 3`, `t = 4`. -/
example : amount 1 2 3 4 + ∫ s in (0)..4, 1 * amount 1 2 3 s = 3 + 2 * 4 :=
  amount_add_eliminated (by norm_num)

/-- Bolus `D = 100`, `CL = 2`, `V = 10`: total AUC `D / CL = 50`. -/
example : ∫ t in Set.Ici 0, concentration 2 10 0 100 t = 50 := by
  rw [integral_Ici_concentration_bolus (by norm_num) (by norm_num)]; norm_num

/-- Finite-horizon AUC over one half-life `T = 5 log 2` (`CL = 2`, `V = 10`, `D = 100`):
`50 (1 - 1/2) = 25`. -/
example : ∫ t in (0)..(5 * log 2), concentration 2 10 0 100 t = 25 := by
  rw [integral_concentration_bolus (by norm_num) (by norm_num), elimRate,
    show -(2 / 10 : ℝ) * (5 * log 2) = -log 2 by ring, exp_neg, exp_log two_pos]
  norm_num

/-- After one half-life the bolus amount is halved: `100 → 50` at `t = t½`. -/
example : amount (1 / 5) 0 100 (halfLife (1 / 5)) = 50 := by
  have h := amount_bolus_add_halfLife (k := 1 / 5) (by norm_num) 100 0
  rw [zero_add, amount_zero] at h
  rw [h]; norm_num

/-- Constant infusion `R = 3`, `CL = 2`, `V = 10`: `C → R / CL = 3/2`. -/
example : Tendsto (concentration 2 10 3 0) atTop (𝓝 (3 / 2)) :=
  tendsto_concentration (by norm_num) (by norm_num) 3 0

/-- Starting empty below `A∞ = 15` (`k = 1/5`, `R = 3`): monotone rise, bounded by `15`. -/
example : Monotone (amount (1 / 5) 3 0) :=
  amount_monotone (by norm_num) (by norm_num [steadyAmount])

example (t : ℝ) : amount (1 / 5) 3 0 t ≤ 15 := by
  have := amount_le_steadyAmount (k := 1 / 5) (R := 3) (A₀ := 0) (by norm_num)
    (by norm_num [steadyAmount]) t
  norm_num [steadyAmount] at this
  exact this

/-- Starting above `A∞ = 15`: monotone decay toward it. -/
example : Antitone (amount (1 / 5) 3 20) :=
  amount_antitone (by norm_num) (by norm_num [steadyAmount])

/-- Boundary `k = 0`, `R = 0`: constant. -/
example : amount 0 0 5 100 = 5 := amount_rate_zero_input_zero 5 100

/-- Boundary `k = 0`, `R = 1`: unbounded, no limit, no constant solution. -/
example : Tendsto (amount 0 1 5) atTop atTop := tendsto_amount_rate_zero_atTop one_pos 5

example : ¬ Tendsto (amount 0 1 5) atTop (𝓝 5) := not_tendsto_amount_rate_zero one_pos 5 5

example : ¬ IsSolution 0 1 (fun _ ↦ 5) := not_isSolution_const_rate_zero one_ne_zero 5

/-- Boundary `k = 1/5`, `R = 0`: exponential washout to `0`. -/
example : Tendsto (amount (1 / 5) 0 100) atTop (𝓝 0) := tendsto_amount_bolus (by norm_num) 100

/-- Uniqueness instance: a solution is determined by its initial value. -/
example {A : ℝ → ℝ} (h : IsSolution (1 / 5) 3 A) (hA : A 0 = 0) :
    A 10 = amount (1 / 5) 3 0 10 := by
  rw [h.eq_amount (by norm_num), hA]

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics
