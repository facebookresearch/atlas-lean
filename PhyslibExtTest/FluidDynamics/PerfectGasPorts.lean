/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import PhyslibExt.FluidDynamics.PerfectGasPorts

/-!
# Perfect-gas stagnation checks

Checks for `PhyslibExt.FluidDynamics.PerfectGasPorts`, mostly for air with `γ = 7/5`,
`R = 287 J/(kg K)` and `cp = 2009/2 J/(kg K)` at `T = 205 K`, `a = 287 m/s` and `u = 574 m/s`
(`M = 2`):

* the fixture values, with the stagnation temperature `T0 = 369 K`;
* the temperature ratio `T0 / T = 9/5` and `T < T0` from the lemmas;
* an isentropic deceleration with `γ = 2`, `R = 1`, `T = 2` and `M = 1`: `p0 / p = 9/4` and
  `ρ0 / ρ = 3/2`;
* at rest the declared stagnation state is the static state;
* the energy balance alone admits a state below the isentropic pressure ratio.

These are elaboration and non-vacuity checks, not new results.
-/

open FluidDynamics.PerfectGasPorts

/-- Fixture: air with `γ = 7/5` and `R = 287` J/(kg K), so `cp = 2009/2` J/(kg K), at `T = 205` K
has the sound speed `a = 287` m/s (`a ^ 2 = γ R T`); at `u = 574` m/s, `M = 2`, the stagnation
energy balance gives `T0 = 369` K, so `T0 / T = 9/5 = 1 + (γ - 1) M ^ 2 / 2` and `T < T0`. -/
example :
    (2009 / 2 : ℝ) = 7 / 5 * 287 / (7 / 5 - 1) ∧ (287 : ℝ) ^ 2 = 7 / 5 * 287 * 205 ∧
      |(574 : ℝ)| / 287 = 2 ∧ (2009 / 2 : ℝ) * 205 + 574 ^ 2 / 2 = 2009 / 2 * 369 ∧
      (369 : ℝ) / 205 = 1 + (7 / 5 - 1) * 2 ^ 2 / 2 ∧ (205 : ℝ) < 369 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- The temperature ratio and `T < T0` at the air fixture. -/
example : (369 : ℝ) / 205 = 1 + (7 / 5 - 1) * 2 ^ 2 / 2 ∧ (205 : ℝ) < 369 :=
  ⟨stagnation_temperature_ratio (γ := 7 / 5) (R := 287) (T := 205) (T0 := 369)
      (cp := 2009 / 2) (a := 287) (u := 574) (M := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    temperature_lt_stagnation (γ := 7 / 5) (R := 287) (T := 205) (T0 := 369)
      (cp := 2009 / 2) (a := 287) (u := 574) (M := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

/-- An isentropic deceleration with `γ = 2`, `R = 1`, `cp = 2`, `T = 2`, `a = u = 2` (`M = 1`)
from `ρ = 1`, `p = 2` to `T0 = 3`, `ρ0 = 3/2`, `p0 = 9/2`: `p0 / p = (3/2) ^ 2` and
`ρ0 / ρ = 3/2`. -/
example : (9 / 2 : ℝ) / 2 = (3 / 2 : ℝ) ^ ((2 : ℝ) / (2 - 1)) ∧
    (3 / 2 : ℝ) / 1 = (3 / 2 : ℝ) ^ ((1 : ℝ) / (2 - 1)) := by
  have hs : (2 : ℝ) / (1 : ℝ) ^ (2 : ℝ) = (9 / 2) / (3 / 2 : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two, Real.rpow_two]
    norm_num
  exact ⟨(stagnation_pressure_ratio (γ := 2) (R := 1) (T := 2) (T0 := 3) (cp := 2) (a := 2)
      (u := 2) (M := 1) (ρ := 1) (ρ0 := 3 / 2) (p := 2) (p0 := 9 / 2) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hs).1,
    (stagnation_density_ratio (γ := 2) (R := 1) (T := 2) (T0 := 3) (cp := 2) (a := 2)
      (u := 2) (M := 1) (ρ := 1) (ρ0 := 3 / 2) (p := 2) (p0 := 9 / 2) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hs).1⟩

/-- At rest (`u = 0`, `M = 0`) every declared stagnation state of the static state `ρ = 1`,
`p = 2`, `T = 2` (with `γ = 2`, `R = 1`, `cp = 2`) is that static state. -/
example {T0 ρ0 p0 : ℝ} (hen : 2 * 2 + 0 ^ 2 / 2 = 2 * T0) (hρ0 : 0 < ρ0)
    (hp0 : p0 = ρ0 * 1 * T0) (hs : (2 : ℝ) / 1 ^ (2 : ℝ) = p0 / ρ0 ^ (2 : ℝ)) :
    T0 = 2 ∧ p0 = 2 ∧ ρ0 = 1 :=
  stagnation_eq_static_of_mach_eq_zero (γ := 2) (R := 1) (T := 2) (cp := 2) (a := 2) (u := 0)
    (M := 0) (ρ := 1) (p := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hen (by norm_num) hρ0 (by norm_num) hp0 hs rfl

/-- The energy balance alone at the air fixture (with `ρ = 1`) admits a state obeying the
ideal-gas law whose pressure ratio is below the isentropic one. -/
example : ∃ ρ0 p0 : ℝ, 0 < ρ0 ∧ p0 = ρ0 * 287 * 369 ∧
    p0 / (1 * 287 * 205) < ((369 : ℝ) / 205) ^ ((7 / 5 : ℝ) / (7 / 5 - 1)) :=
  stagnation_energy_not_isentropic (γ := 7 / 5) (T := 205) (T0 := 369) (cp := 2009 / 2)
    (a := 287) (u := 574) (M := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl
