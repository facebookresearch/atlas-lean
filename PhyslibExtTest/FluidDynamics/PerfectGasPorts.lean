/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
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
* the energy balance alone admits a state below the isentropic pressure ratio;
* the isentropic mass flux of air at `M = 1/2`, `1` and `2` (`4000/9261`, `125/216` and `250/729`
  times `p0 √(γ / (R T0))`), the area ratios `343/256` and `27/16`, and a supersonic Mach number
  in `(1, 2)` with the flux of `M = 1/2`;
* the flux bridge at the sonic isentropic state, the sonic maximum and the area ratio from equal
  mass flow, with every hypothesis discharged, and zero flux at rest.

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

/-! ## The isentropic mass flux -/

namespace PhyslibExtTest.FluidDynamics.PerfectGasPorts

/-- **Air values** (`γ = 7/5`): the subsonic `M = 1/2`, sonic `M = 1` and supersonic `M = 2`
fluxes are `4000/9261`, `125/216` and `250/729` times `p0 √(γ / (R T0))`. -/
lemma isentropicMassFlux_air (p0 T0 R : ℝ) :
    isentropicMassFlux p0 T0 R (7 / 5) (1 / 2) =
        p0 * Real.sqrt (7 / 5 / (R * T0)) * (4000 / 9261) ∧
      isentropicMassFlux p0 T0 R (7 / 5) 1 = p0 * Real.sqrt (7 / 5 / (R * T0)) * (125 / 216) ∧
      isentropicMassFlux p0 T0 R (7 / 5) 2 = p0 * Real.sqrt (7 / 5 / (R * T0)) * (250 / 729) := by
  have hexp : (-(7/5 + 1) / (2 * (7/5 - 1)) : ℝ) = -3 := by norm_num
  have h1 : isentropicMassFlux p0 T0 R (7 / 5) (1 / 2) =
      p0 * Real.sqrt (7 / 5 / (R * T0)) * (4000 / 9261) := by
    have hX : (1 + (7/5 - 1) * (1/2 : ℝ) ^ 2 / 2 : ℝ) = 21/20 := by norm_num
    unfold isentropicMassFlux
    rw [hexp, hX]
    have hrpow : ((21/20 : ℝ) ^ (-3 : ℝ)) = 8000/9261 := by
      have hexp2 : (-3 : ℝ) = -((3 : ℕ) : ℝ) := by norm_num
      rw [hexp2, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 21/20), Real.rpow_natCast]
      norm_num
    rw [hrpow]
    ring
  have h2 : isentropicMassFlux p0 T0 R (7 / 5) 1 =
      p0 * Real.sqrt (7 / 5 / (R * T0)) * (125 / 216) := by
    have hX : (1 + (7/5 - 1) * (1 : ℝ) ^ 2 / 2 : ℝ) = 6/5 := by norm_num
    unfold isentropicMassFlux
    rw [hexp, hX]
    have hrpow : ((6/5 : ℝ) ^ (-3 : ℝ)) = 125/216 := by
      have hexp2 : (-3 : ℝ) = -((3 : ℕ) : ℝ) := by norm_num
      rw [hexp2, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 6/5), Real.rpow_natCast]
      norm_num
    rw [hrpow]
    ring
  have h3 : isentropicMassFlux p0 T0 R (7 / 5) 2 =
      p0 * Real.sqrt (7 / 5 / (R * T0)) * (250 / 729) := by
    have hX : (1 + (7/5 - 1) * (2 : ℝ) ^ 2 / 2 : ℝ) = 9/5 := by norm_num
    unfold isentropicMassFlux
    rw [hexp, hX]
    have hrpow : ((9/5 : ℝ) ^ (-3 : ℝ)) = 125/729 := by
      have hexp2 : (-3 : ℝ) = -((3 : ℕ) : ℝ) := by norm_num
      rw [hexp2, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 9/5), Real.rpow_natCast]
      norm_num
    rw [hrpow]
    ring
  exact ⟨h1, h2, h3⟩

/-- **Air area ratios** (`γ = 7/5`): `A / A* = 343/256` at the subsonic `M = 1/2` and `27/16` at
the supersonic `M = 2`, both above `1`. -/
example {p0 T0 R : ℝ} (hp0 : 0 < p0) (hT0 : 0 < T0) (hR : 0 < R) :
    isentropicMassFlux p0 T0 R (7 / 5) 1 / isentropicMassFlux p0 T0 R (7 / 5) (1 / 2) =
        343 / 256 ∧
      isentropicMassFlux p0 T0 R (7 / 5) 1 / isentropicMassFlux p0 T0 R (7 / 5) 2 = 27 / 16 := by
  obtain ⟨h12, h1, h2⟩ := isentropicMassFlux_air p0 T0 R
  have hsqrt : 0 < Real.sqrt (7 / 5 / (R * T0)) := by
    apply Real.sqrt_pos.mpr
    positivity
  have hC : p0 * Real.sqrt (7 / 5 / (R * T0)) ≠ 0 := ne_of_gt (mul_pos hp0 hsqrt)
  rw [h1, h12, h2]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- **Both sides of the sonic maximum** (air, `γ = 7/5`): a supersonic Mach number in `(1, 2)`
carries the flux of the subsonic `M = 1/2`, hence the same area ratio `343/256`. -/
example {p0 T0 R : ℝ} (hp0 : 0 < p0) (hT0 : 0 < T0) (hR : 0 < R) :
    ∃ M₂ : ℝ, 1 < M₂ ∧ M₂ < 2 ∧
      isentropicMassFlux p0 T0 R (7 / 5) M₂ = isentropicMassFlux p0 T0 R (7 / 5) (1 / 2) := by
  obtain ⟨h12, h1, h2⟩ := isentropicMassFlux_air p0 T0 R
  have hγ : (1:ℝ) < 7 / 5 := by norm_num
  have hsqrt : 0 < Real.sqrt (7 / 5 / (R * T0)) := by
    apply Real.sqrt_pos.mpr
    positivity
  have hC : 0 < p0 * Real.sqrt (7 / 5 / (R * T0)) := mul_pos hp0 hsqrt
  have hlt1 : (250 / 729 : ℝ) < 4000 / 9261 := by norm_num
  have hlt2 : (4000 / 9261 : ℝ) < 125 / 216 := by norm_num
  have hG2_lt : isentropicMassFlux p0 T0 R (7 / 5) 2 <
      isentropicMassFlux p0 T0 R (7 / 5) (1 / 2) := by
    rw [h2, h12]
    exact mul_lt_mul_of_pos_left hlt1 hC
  have hG12_lt : isentropicMassFlux p0 T0 R (7 / 5) (1 / 2) <
      isentropicMassFlux p0 T0 R (7 / 5) 1 := by
    rw [h12, h1]
    exact mul_lt_mul_of_pos_left hlt2 hC
  have hcont : ContinuousOn (isentropicMassFlux p0 T0 R (7 / 5)) (Set.Icc 1 2) := fun x _ =>
    (hasDerivAt_isentropicMassFlux hγ p0 T0 R x).continuousAt.continuousWithinAt
  have hmem : isentropicMassFlux p0 T0 R (7 / 5) (1 / 2) ∈
      Set.Ioo (isentropicMassFlux p0 T0 R (7 / 5) 2)
        (isentropicMassFlux p0 T0 R (7 / 5) 1) := ⟨hG2_lt, hG12_lt⟩
  have hsub := intermediate_value_Ioo' (a := (1:ℝ)) (b := (2:ℝ)) (by norm_num) hcont
  have himg := hsub hmem
  obtain ⟨M₂, hM₂mem, hM₂eq⟩ := himg
  exact ⟨M₂, hM₂mem.1, hM₂mem.2, hM₂eq⟩

/-- The flux of the isentropic state at the sonic deceleration above (`γ = 2`, `R = 1`, `T = 2`,
`a = u = 2`, `M = 1`, `T0 = 3`, `ρ = 1`, `p0 = 9/2`): `ρ |u| = 2 = G(1)`. -/
example : (1 : ℝ) * |(2 : ℝ)| = isentropicMassFlux (9 / 2) 3 1 2 1 := by
  refine massFlux_eq_isentropicMassFlux (γ := 2) (R := 1) (T := 2) (T0 := 3) (cp := 2) (a := 2)
    (u := 2) (M := 1) (ρ := 1) (ρ0 := 3 / 2) (p := 2) (p0 := 9 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
  norm_num

/-- The sonic maximum for air: `G(2) < G(1)` and `G(1/2) < G(1)`. -/
example : isentropicMassFlux 1 1 1 (7 / 5) 2 < isentropicMassFlux 1 1 1 (7 / 5) 1 ∧
    isentropicMassFlux 1 1 1 (7 / 5) (1 / 2) < isentropicMassFlux 1 1 1 (7 / 5) 1 :=
  ⟨isentropicMassFlux_lt_sonic (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num),
    isentropicMassFlux_lt_sonic (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)⟩

/-- The area ratio from equal mass flow for air at `M = 2`: sections `A = 27` and `A* = 16`
carry the same flow, so `A / A* = G(1) / G(2) = 27/16 ≥ 1`. -/
example : (27 : ℝ) / 16 = isentropicMassFlux 1 1 1 (7 / 5) 1 / isentropicMassFlux 1 1 1 (7 / 5) 2 ∧
    1 ≤ (27 : ℝ) / 16 := by
  obtain ⟨_, h1, h2⟩ := isentropicMassFlux_air 1 1 1
  refine area_ratio_eq_and_one_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_
  rw [h1, h2]
  ring

/-- At rest the flux vanishes and the area-ratio quotient fails `≥ 1`. -/
example : isentropicMassFlux 1 1 1 (7 / 5) 0 = 0 := (isentropicMassFlux_zero 1 1 1 (7 / 5)).1

end PhyslibExtTest.FluidDynamics.PerfectGasPorts
