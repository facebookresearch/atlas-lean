/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
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
  mass flow, with every hypothesis discharged, and zero flux at rest;
* stationary area at a sonic station, for `γ = 2`, `R = 1`, `T0 = 3`, `ρ0 = 3` and the mass flow
  `4`: a smooth flow through `M = 1`, which meets every hypothesis of the stationary-area lemma at
  its sonic station, and a subsonic throat, a strict area minimum with `A' = 0`, `u' = 0` and
  `M < 1`;
* normal shocks of air (`γ = 7/5`): at `M1 = 2` the distinct branch has `ρ2 / ρ1 = 8/3`,
  `p2 / p1 = 9/2` and `T2 / T1 = 27/16`, and an explicit downstream state solves the jump
  conditions; at `M1 = 1/4`, below the threshold `1/7`, the distinct pressure ratio is `-3/32`
  and every positive solution is the upstream state itself.
* the specific entropy change of an isothermal doubling of the specific volume (`R log 2`) and of
  heating at constant specific volume (`cv log 2`);
* entropy selection for air (`γ = 7/5`, `R = 1`): the entropy jump vanishes at `m = 1`, is
  positive at `M1 = 2`, negative at `M1 = 1/2` and has the derivative `35/216` at `m = 4`; the
  compression shock at `M1 = 2` raises the entropy, in the `(T, p)` form and as `R` times the
  branch jump, while the expansion root at `M1 = 1/2` (`ρ2 = 2/5`, `u2 = 7/4`, `p2 = 1/8`,
  `T2 = 5/16`) solves the jump conditions but lowers it; with isentropic stagnation states on both
  sides the stagnation pressure falls across the compression shock and rises across the expansion
  root.

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

/-! ## The area-velocity relation and stationary area -/

section AreaVelocity

open Set
open scoped ContDiff Topology

/-- **A smooth parameterization through `M = 1`.** For `γ = 2`, `R = 1`, `cp = 2`, `T0 = 3`,
`ρ0 = 3`, `p0 = 9` and `ṁ = 4`, the speed `u = 2 + x` with `T = 3 - u ^ 2 / 4`, `ρ = T`,
`p = T ^ 2` and `A = 4 / (u T)` is a smooth steady isentropic quasi-one-dimensional flow on
`(-1, 1)`: subsonic for `x < 0`, sonic at `x = 0` and supersonic for `x > 0`, where
`M = |u| / √(γ R T)`; at the sonic station `A' = 0` and `u' = 1 ≠ 0`. -/
lemma transonic_parameterization :
    ∃ A ρ u T p : ℝ → ℝ,
      (∀ x ∈ Ioo (-1 : ℝ) 1, 0 < A x ∧ 0 < ρ x ∧ 0 < u x ∧ 0 < T x ∧ p x = ρ x * 1 * T x ∧
        p x / ρ x ^ (2 : ℝ) = 9 / 3 ^ (2 : ℝ) ∧ 2 * T x + u x ^ 2 / 2 = 2 * 3 ∧
        ρ x * u x * A x = 4) ∧
      ContDiffOn ℝ ∞ A (Ioo (-1) 1) ∧ ContDiffOn ℝ ∞ ρ (Ioo (-1) 1) ∧
      ContDiffOn ℝ ∞ u (Ioo (-1) 1) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 0, |u x| / Real.sqrt (2 * 1 * T x) < 1) ∧
      |u 0| / Real.sqrt (2 * 1 * T 0) = 1 ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, 1 < |u x| / Real.sqrt (2 * 1 * T x)) ∧
      HasDerivAt A 0 0 ∧ HasDerivAt u 1 0 := by
  refine ⟨fun x => 4 / ((2 + x) * (3 - (2 + x) ^ 2 / 4)), fun x => 3 - (2 + x) ^ 2 / 4,
    fun x => 2 + x, fun x => 3 - (2 + x) ^ 2 / 4, fun x => (3 - (2 + x) ^ 2 / 4) ^ 2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := hx
    have hs : 0 < 2 + x := by linarith
    have hT : 0 < 3 - (2 + x) ^ 2 / 4 := by nlinarith
    refine ⟨by positivity, hT, hs, hT, by ring, ?_, by ring, ?_⟩
    · rw [Real.rpow_two, Real.rpow_two, div_self (pow_ne_zero 2 hT.ne')]
      norm_num
    · change (3 - (2 + x) ^ 2 / 4) * (2 + x) * (4 / ((2 + x) * (3 - (2 + x) ^ 2 / 4))) = 4
      set t := 3 - (2 + x) ^ 2 / 4
      field_simp
  · refine ContDiffOn.div contDiffOn_const (by fun_prop) fun x hx => ?_
    have hs : 0 < 2 + x := by linarith [hx.1]
    have hT : 0 < 3 - (2 + x) ^ 2 / 4 := by nlinarith [hx.1, hx.2]
    positivity
  · exact (by fun_prop : ContDiff ℝ ∞ fun x : ℝ => 3 - (2 + x) ^ 2 / 4).contDiffOn
  · exact (by fun_prop : ContDiff ℝ ∞ fun x : ℝ => 2 + x).contDiffOn
  · intro x hx
    obtain ⟨h1, h2⟩ := hx
    have hs : 0 < 2 + x := by linarith
    have hT : 0 < 2 * 1 * (3 - (2 + x) ^ 2 / 4) := by nlinarith
    rw [abs_of_pos hs, div_lt_one (Real.sqrt_pos.mpr hT), Real.lt_sqrt hs.le]
    nlinarith
  · have h : Real.sqrt (2 * 1 * (3 - (2 + 0) ^ 2 / 4)) = 2 := by
      rw [show (2 * 1 * (3 - (2 + 0) ^ 2 / 4) : ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    simp only [h]
    norm_num
  · intro x hx
    obtain ⟨h1, h2⟩ := hx
    have hs : 0 < 2 + x := by linarith
    have hT : 0 < 2 * 1 * (3 - (2 + x) ^ 2 / 4) := by nlinarith
    rw [abs_of_pos hs, one_lt_div (Real.sqrt_pos.mpr hT), Real.sqrt_lt' hs]
    nlinarith
  · have hs : HasDerivAt (fun x : ℝ => 2 + x) 1 0 := (hasDerivAt_id' 0).const_add 2
    have hT : HasDerivAt (fun x : ℝ => 3 - (2 + x) ^ 2 / 4) (-(2 * (2 + 0) ^ (2 - 1) * 1 / 4)) 0 :=
      ((hs.pow 2).div_const 4).const_sub 3
    have hg := hs.mul hT
    have h := (hasDerivAt_const (0 : ℝ) (4 : ℝ)).div hg (by norm_num)
    convert h using 1
    norm_num
  · exact (hasDerivAt_id' 0).const_add 2

/-- **A subsonic throat.** For the same gas and stagnation state, the speed `u = 1 - x ^ 2` with
`T = 3 - u ^ 2 / 4`, `ρ = T`, `p = T ^ 2` and `A = 4 / (u T)` is a smooth steady isentropic
quasi-one-dimensional flow on `(-1, 1)` whose area has a strict minimum at `x = 0`, where
`A' = 0` and `u' = 0` but `M < 1`: a throat with `A' = 0` need not be sonic. -/
lemma subsonic_throat :
    ∃ A ρ u T p : ℝ → ℝ,
      (∀ x ∈ Ioo (-1 : ℝ) 1, 0 < A x ∧ 0 < ρ x ∧ 0 < u x ∧ 0 < T x ∧ p x = ρ x * 1 * T x ∧
        p x / ρ x ^ (2 : ℝ) = 9 / 3 ^ (2 : ℝ) ∧ 2 * T x + u x ^ 2 / 2 = 2 * 3 ∧
        ρ x * u x * A x = 4) ∧
      ContDiffOn ℝ ∞ A (Ioo (-1) 1) ∧ ContDiffOn ℝ ∞ ρ (Ioo (-1) 1) ∧
      ContDiffOn ℝ ∞ u (Ioo (-1) 1) ∧
      HasDerivAt A 0 0 ∧ HasDerivAt u 0 0 ∧ |u 0| / Real.sqrt (2 * 1 * T 0) < 1 ∧
      ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 → A 0 < A x := by
  refine ⟨fun x => 4 / ((1 - x ^ 2) * (3 - (1 - x ^ 2) ^ 2 / 4)),
    fun x => 3 - (1 - x ^ 2) ^ 2 / 4, fun x => 1 - x ^ 2, fun x => 3 - (1 - x ^ 2) ^ 2 / 4,
    fun x => (3 - (1 - x ^ 2) ^ 2 / 4) ^ 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := hx
    have hu : 0 < 1 - x ^ 2 := by nlinarith
    have hu1 : 1 - x ^ 2 ≤ 1 := by nlinarith
    have hT : 0 < 3 - (1 - x ^ 2) ^ 2 / 4 := by nlinarith
    refine ⟨by positivity, hT, hu, hT, by ring, ?_, by ring, ?_⟩
    · rw [Real.rpow_two, Real.rpow_two, div_self (pow_ne_zero 2 hT.ne')]
      norm_num
    · change (3 - (1 - x ^ 2) ^ 2 / 4) * (1 - x ^ 2) *
          (4 / ((1 - x ^ 2) * (3 - (1 - x ^ 2) ^ 2 / 4))) = 4
      set t := 3 - (1 - x ^ 2) ^ 2 / 4
      set v := 1 - x ^ 2
      field_simp
  · refine ContDiffOn.div contDiffOn_const (by fun_prop) fun x hx => ?_
    have hu : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hT : 0 < 3 - (1 - x ^ 2) ^ 2 / 4 := by nlinarith [hx.1, hx.2]
    positivity
  · exact (by fun_prop : ContDiff ℝ ∞ fun x : ℝ => 3 - (1 - x ^ 2) ^ 2 / 4).contDiffOn
  · exact (by fun_prop : ContDiff ℝ ∞ fun x : ℝ => 1 - x ^ 2).contDiffOn
  · have hu : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * 0 ^ (2 - 1) * 1)) 0 :=
      ((hasDerivAt_id' 0).pow 2).const_sub 1
    have hT : HasDerivAt (fun x : ℝ => 3 - (1 - x ^ 2) ^ 2 / 4)
        (-(2 * (1 - 0 ^ 2) ^ (2 - 1) * -(2 * 0 ^ (2 - 1) * 1) / 4)) 0 :=
      ((hu.pow 2).div_const 4).const_sub 3
    have hg := hu.mul hT
    have h := (hasDerivAt_const (0 : ℝ) (4 : ℝ)).div hg (by norm_num)
    convert h using 1
    norm_num
  · have h := ((hasDerivAt_id' (0 : ℝ)).pow 2).const_sub 1
    convert h using 1
    norm_num
  · change |(1 : ℝ) - 0 ^ 2| / Real.sqrt (2 * 1 * (3 - (1 - 0 ^ 2) ^ 2 / 4)) < 1
    have e : (2 * 1 * (3 - (1 - 0 ^ 2) ^ 2 / 4) : ℝ) = 11 / 2 := by norm_num
    have h : (1 : ℝ) < Real.sqrt (11 / 2) := by
      rw [Real.lt_sqrt zero_le_one]
      norm_num
    rw [e, show |(1 : ℝ) - 0 ^ 2| = 1 by norm_num, div_lt_one (by linarith)]
    exact h
  · intro x hx hx0
    obtain ⟨h1, h2⟩ := hx
    have hx2 : 0 < x ^ 2 := by positivity
    have hu : 0 < 1 - x ^ 2 := by nlinarith
    have hu1 : 1 - x ^ 2 < 1 := by linarith
    have hg : 0 < (1 - x ^ 2) * (3 - (1 - x ^ 2) ^ 2 / 4) := by
      have hT : 0 < 3 - (1 - x ^ 2) ^ 2 / 4 := by nlinarith
      positivity
    have hlt : (1 - x ^ 2) * (3 - (1 - x ^ 2) ^ 2 / 4) <
        (1 - 0 ^ 2) * (3 - (1 - 0 ^ 2) ^ 2 / 4) := by
      nlinarith [mul_pos hu (sub_pos.mpr hu1), sq_nonneg (1 - x ^ 2)]
    exact div_lt_div_of_pos_left (by norm_num) hg hlt

/-- The stationary-area lemma applies to an actual flow: the transonic parameterization meets
every hypothesis of `area_deriv_eq_zero_of_mach_eq_one` at its sonic station `x₀ = 0`, with the
sound speed `a = √(2 T 0)` and `M = 1`, so the lemma, not the construction, gives `A' = 0`
there. -/
example : ∃ A : ℝ → ℝ, HasDerivAt A (deriv A 0) 0 ∧ deriv A 0 = 0 := by
  obtain ⟨A, ρ, u, T, p, hrel, hA, hρ, hu, -, hM0, -, -, -⟩ := transonic_parameterization
  have hmem : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have ev : ∀ᶠ x in 𝓝 (0 : ℝ), x ∈ Ioo (-1 : ℝ) 1 := hmem
  obtain ⟨hA0, -, hu0, hT0, -, -, -, -⟩ := hrel 0 ⟨by norm_num, by norm_num⟩
  have hdA : DifferentiableAt ℝ A 0 := (hA.contDiffAt hmem).differentiableAt (by norm_num)
  have hdρ : DifferentiableAt ℝ ρ 0 := (hρ.contDiffAt hmem).differentiableAt (by norm_num)
  have hdu : DifferentiableAt ℝ u 0 := (hu.contDiffAt hmem).differentiableAt (by norm_num)
  have hsq : 0 ≤ 2 * 1 * T 0 := by positivity
  refine ⟨A, hdA.hasDerivAt, ?_⟩
  exact area_deriv_eq_zero_of_mach_eq_one (γ := 2) (R := 1) (cp := 2) (T0 := 3) (ρ0 := 3)
    (p0 := 9) (mdot := 4) (a := Real.sqrt (2 * 1 * T 0)) (M := |u 0| / Real.sqrt (2 * 1 * T 0))
    (x₀ := 0) (A := A) (ρ := ρ) (u := u) (T := T) (p := p)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (ev.mono fun x hx => (hrel x hx).2.2.2.1) (ev.mono fun x hx => (hrel x hx).2.1)
    (ev.mono fun x hx => (hrel x hx).2.2.2.2.1)
    (ev.mono fun x hx => by
      have h := (hrel x hx).2.2.2.2.2.1
      norm_num at h ⊢
      exact h)
    (ev.mono fun x hx => (hrel x hx).2.2.2.2.2.2.1)
    (ev.mono fun x hx => (hrel x hx).2.2.2.2.2.2.2)
    hu0 hA0 (Real.sq_sqrt hsq) rfl hdA.hasDerivAt hdρ.hasDerivAt hdu.hasDerivAt hM0

end AreaVelocity

/-! ## Normal-shock branches -/

/-- **`M1 = 2`, `γ = 7/5` gives compression.** The distinct branch has `ρ2 / ρ1 = 8/3`,
`p2 / p1 = 9/2` and `T2 / T1 = 27/16`, all above `1`. With `R = 1`, `ρ1 = 7/5`, `T1 = 5/7` (so
`p1 = 1` and `a1 = 1`) and `u1 = 2`, the downstream state `ρ2 = 56/15`, `u2 = 3/4`, `p2 = 9/2`,
`T2 = 135/112` solves the jump conditions. -/
lemma normalShock_fixture_mach_two :
    shockDensityRatio (7 / 5) (2 ^ 2) = 8 / 3 ∧ shockPressureRatio (7 / 5) (2 ^ 2) = 9 / 2 ∧
      shockTemperatureRatio (7 / 5) (2 ^ 2) = 27 / 16 ∧
      IsNormalShockJump (7 / 5) 1 (7 / 5) 2 1 (5 / 7) (56 / 15) (3 / 4) (9 / 2) (135 / 112) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold shockDensityRatio; norm_num
  · unfold shockPressureRatio; norm_num
  · unfold shockTemperatureRatio shockDensityRatio shockPressureRatio; norm_num
  · unfold IsNormalShockJump; norm_num

/-- **Below the pressure-positivity threshold the second root is not a physical state.** At
`γ = 7/5` the threshold `(γ - 1) / (2 γ)` is `1/7`; at `M1 = 1/4` (`m = 1/16`) the distinct
pressure ratio is `-3/32`. With the upstream state of `normalShock_fixture_mach_two` moving at
`u1 = 1/4`, every downstream state with positive density and temperature that satisfies the jump
conditions is the upstream state itself. -/
example :
    ((7 / 5 : ℝ) - 1) / (2 * (7 / 5)) = 1 / 7 ∧ shockPressureRatio (7 / 5) ((1 / 4) ^ 2) = -3 / 32 ∧
      ∀ ρ2 u2 p2 T2 : ℝ, 0 < ρ2 → 0 < T2 →
        IsNormalShockJump (7 / 5) 1 (7 / 5) (1 / 4) 1 (5 / 7) ρ2 u2 p2 T2 →
          ρ2 = 7 / 5 ∧ u2 = 1 / 4 ∧ p2 = 1 ∧ T2 = 5 / 7 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num
  · unfold shockPressureRatio; norm_num
  · intro ρ2 u2 p2 T2 hρ2 hT2 hjump
    have hγ : (1 : ℝ) < 7 / 5 := by norm_num
    have hR : (0 : ℝ) < 1 := by norm_num
    have hρ1 : (0 : ℝ) < 7 / 5 := by norm_num
    have hT1 : (0 : ℝ) < 5 / 7 := by norm_num
    have ha1 : (1 : ℝ) ^ 2 = (7 / 5) * 1 * (5 / 7) := by norm_num
    have hM1 : (1 / 4 : ℝ) = |(1 / 4 : ℝ)| / (1 : ℝ) := by norm_num
    have hclass := normalShock_classification hγ hR hρ1 hT1 hρ2 hT2 ha1 hM1 hjump
    rcases hclass with htrivial | hdistinct
    · exact htrivial
    · exfalso
      obtain ⟨_, _, _, hthresh⟩ := hdistinct
      revert hthresh
      norm_num

/-! ## Entropy selection of the normal-shock branch -/

/-- The specific entropy change of an isothermal doubling of the specific volume, here with
`cv = 5 / 2`, `R = 1` and `T = 300`, is `R log 2`; heating at constant specific volume from `300` to
`600` gives `cv log 2`. -/
example : specificEntropyChange (5 / 2) 1 300 1 300 2 = Real.log 2 ∧
    specificEntropyChange (5 / 2) 1 300 1 600 1 = 5 / 2 * Real.log 2 := by
  unfold specificEntropyChange
  norm_num

/-- **Compression shock.** `γ = 7 / 5`, `R = 1`, upstream `ρ1 = 7 / 5`, `u1 = 2`, `p1 = 1`,
`T1 = 5 / 7` (`a1 = 1`, `M1 = 2`), downstream `ρ2 = 56 / 15`, `u2 = 3 / 4`, `p2 = 9 / 2`,
`T2 = 135 / 112`: the jump conditions hold and the entropy rises. -/
lemma normalShock_fixture_compression :
    IsNormalShockJump (7 / 5) 1 (7 / 5) 2 1 (5 / 7) (56 / 15) (3 / 4) (9 / 2) (135 / 112) ∧
      0 < specificEntropyChange (1 / (7 / 5 - 1)) 1 (5 / 7) (1 / (7 / 5)) (135 / 112)
        (1 / (56 / 15)) := by
  have hjump :
      IsNormalShockJump (7 / 5) 1 (7 / 5) 2 1 (5 / 7) (56 / 15) (3 / 4) (9 / 2) (135 / 112) := by
    unfold IsNormalShockJump
    norm_num
  refine ⟨hjump, ?_⟩
  have h := normalShock_entropy_pos_iff (a1 := 1) (M1 := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hjump (by norm_num)
  exact h.1.mpr (by norm_num)

/-- **Expansion root.** The same upstream gas at `u1 = 1 / 2` (`M1 = 1 / 2`, above the threshold
`1 / 7` of `M1 ^ 2`) and the downstream `ρ2 = 2 / 5`, `u2 = 7 / 4`, `p2 = 1 / 8`, `T2 = 5 / 16`:
a positive state that solves the jump conditions, but the entropy falls, so the root is not
entropy-admissible. -/
lemma normalShock_fixture_expansion :
    IsNormalShockJump (7 / 5) 1 (7 / 5) (1 / 2) 1 (5 / 7) (2 / 5) (7 / 4) (1 / 8) (5 / 16) ∧
      specificEntropyChange (1 / (7 / 5 - 1)) 1 (5 / 7) (1 / (7 / 5)) (5 / 16)
        (1 / (2 / 5)) < 0 := by
  have hjump :
      IsNormalShockJump (7 / 5) 1 (7 / 5) (1 / 2) 1 (5 / 7) (2 / 5) (7 / 4) (1 / 8) (5 / 16) := by
    unfold IsNormalShockJump
    norm_num
  refine ⟨hjump, ?_⟩
  have h := normalShock_entropy_pos_iff (a1 := 1) (M1 := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hjump (by norm_num)
  exact h.2.mpr (by norm_num)

/-- The entropy jump at `γ = 7/5`: zero at `m = 1`, positive at `M1 = 2` and negative at
`M1 = 1/2`, above the threshold `1/7`; at `m = 4` its derivative is `35/216`. -/
example : shockEntropyJump (7 / 5) 1 = 0 ∧ 0 < shockEntropyJump (7 / 5) (2 ^ 2) ∧
    shockEntropyJump (7 / 5) ((1 / 2) ^ 2) < 0 ∧
    HasDerivAt (shockEntropyJump (7 / 5)) (35 / 216) 4 := by
  refine ⟨shockEntropyJump_one (by norm_num),
    (shockEntropyJump_pos_iff (γ := 7 / 5) (m := 2 ^ 2) (by norm_num) (by norm_num)).1.mpr
      (by norm_num),
    (shockEntropyJump_pos_iff (γ := 7 / 5) (m := (1 / 2) ^ 2) (by norm_num) (by norm_num)).2.mpr
      (by norm_num), ?_⟩
  convert hasDerivAt_shockEntropyJump (γ := 7 / 5) (m := 4) (by norm_num) (by norm_num) using 1
  norm_num

/-- At the compression fixture the entropy change has the `(T, p)` form
`cp log (T2 / T1) - R log (p2 / p1)` and is `R` times the branch jump at `M1 ^ 2 = 4`. -/
example :
    specificEntropyChange (1 / (7 / 5 - 1)) 1 (5 / 7) (1 / (7 / 5)) (135 / 112)
        (1 / (56 / 15)) =
        7 / 5 * 1 / (7 / 5 - 1) * Real.log ((135 / 112) / (5 / 7)) - 1 * Real.log ((9 / 2) / 1) ∧
      specificEntropyChange (1 / (7 / 5 - 1)) 1 (5 / 7) (1 / (7 / 5)) (135 / 112)
        (1 / (56 / 15)) = 1 * shockEntropyJump (7 / 5) (2 ^ 2) := by
  refine ⟨specificEntropyChange_perfectGas (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), ?_⟩
  exact (normalShock_entropyChange (a1 := 1) (M1 := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    normalShock_fixture_compression.1 (by norm_num)).2.2

/-- Every positive ideal-gas state has an isentropic stagnation state: `T0` from the energy
balance, `ρ0 = ρ (T0 / T) ^ (1 / (γ - 1))` and `p0 = ρ0 R T0`. -/
private lemma exists_isentropic_stagnation {γ R ρ u p T : ℝ} (hγ : 1 < γ) (hR : 0 < R)
    (hρ : 0 < ρ) (hT : 0 < T) (hp : p = ρ * R * T) :
    ∃ ρ0 p0 T0 : ℝ, γ * R / (γ - 1) * T + u ^ 2 / 2 = γ * R / (γ - 1) * T0 ∧ 0 < ρ0 ∧
      p0 = ρ0 * R * T0 ∧ p / ρ ^ γ = p0 / ρ0 ^ γ := by
  have hγ1 : 0 < γ - 1 := sub_pos.mpr hγ
  have hcp : 0 < γ * R / (γ - 1) := div_pos (mul_pos (by linarith) hR) hγ1
  obtain ⟨T0, hT0⟩ : ∃ T0 : ℝ, T0 = T + u ^ 2 / (2 * (γ * R / (γ - 1))) := ⟨_, rfl⟩
  have hT0pos : 0 < T0 := by rw [hT0]; positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = T0 / T := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; exact div_pos hT0pos hT
  have hT0c : T0 = c * T := by rw [hc]; field_simp
  have hca : 0 < c ^ (1 / (γ - 1)) := Real.rpow_pos_of_pos hcpos _
  have hkey : c ^ (1 / (γ - 1) * γ) = c ^ (1 / (γ - 1)) * c := by
    rw [← Real.rpow_add_one hcpos.ne']
    congr 1
    field_simp
    ring
  refine ⟨ρ * c ^ (1 / (γ - 1)), ρ * c ^ (1 / (γ - 1)) * R * T0, T0, ?_, mul_pos hρ hca, rfl, ?_⟩
  · rw [hT0]
    field_simp
  · rw [hp, hT0c, Real.mul_rpow hρ.le hca.le, ← Real.rpow_mul hcpos.le, hkey]
    field_simp

/-- Across the compression shock at `M1 = 2`, with isentropic stagnation states on both sides, the
stagnation temperatures agree and the stagnation pressure falls. -/
example : ∃ ρ01 p01 T01 ρ02 p02 T02 : ℝ,
    (7 / 5 * 1 / (7 / 5 - 1) * (5 / 7) + 2 ^ 2 / 2 = 7 / 5 * 1 / (7 / 5 - 1) * T01 ∧
      0 < ρ01 ∧ p01 = ρ01 * 1 * T01 ∧ 1 / (7 / 5 : ℝ) ^ (7 / 5 : ℝ) = p01 / ρ01 ^ (7 / 5 : ℝ)) ∧
    (7 / 5 * 1 / (7 / 5 - 1) * (135 / 112) + (3 / 4) ^ 2 / 2 = 7 / 5 * 1 / (7 / 5 - 1) * T02 ∧
      0 < ρ02 ∧ p02 = ρ02 * 1 * T02 ∧
      9 / 2 / (56 / 15 : ℝ) ^ (7 / 5 : ℝ) = p02 / ρ02 ^ (7 / 5 : ℝ)) ∧
    T02 = T01 ∧ p02 < p01 := by
  obtain ⟨ρ01, p01, T01, hen1, hρ01, hp01, hs1⟩ := exists_isentropic_stagnation (γ := 7 / 5)
    (R := 1) (ρ := 7 / 5) (u := 2) (p := 1) (T := 5 / 7) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨ρ02, p02, T02, hen2, hρ02, hp02, hs2⟩ := exists_isentropic_stagnation (γ := 7 / 5)
    (R := 1) (ρ := 56 / 15) (u := 3 / 4) (p := 9 / 2) (T := 135 / 112) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hjump := normalShock_fixture_compression.1
  obtain ⟨hT0, -⟩ := normalShock_stagnationPressure_ratio (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hjump hen1 hen2 hρ01 hρ02 hp01 hp02
    hs1 hs2
  have hsel := normalShock_totalPressure_selection (a1 := 1) (M1 := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hjump (by norm_num) hen1 hen2 hρ01 hρ02 hp01 hp02 hs1 hs2
  exact ⟨ρ01, p01, T01, ρ02, p02, T02, ⟨hen1, hρ01, hp01, hs1⟩, ⟨hen2, hρ02, hp02, hs2⟩, hT0,
    hsel.1 (by norm_num)⟩

/-- Across the expansion root at `M1 = 1/2`, with isentropic stagnation states on both sides, the
stagnation pressure rises while the entropy falls: the root solves the jump conditions but is not
entropy-admissible. -/
example : ∃ ρ01 p01 T01 ρ02 p02 T02 : ℝ,
    (7 / 5 * 1 / (7 / 5 - 1) * (5 / 7) + (1 / 2) ^ 2 / 2 = 7 / 5 * 1 / (7 / 5 - 1) * T01 ∧
      0 < ρ01 ∧ p01 = ρ01 * 1 * T01 ∧ 1 / (7 / 5 : ℝ) ^ (7 / 5 : ℝ) = p01 / ρ01 ^ (7 / 5 : ℝ)) ∧
    (7 / 5 * 1 / (7 / 5 - 1) * (5 / 16) + (7 / 4) ^ 2 / 2 = 7 / 5 * 1 / (7 / 5 - 1) * T02 ∧
      0 < ρ02 ∧ p02 = ρ02 * 1 * T02 ∧
      1 / 8 / (2 / 5 : ℝ) ^ (7 / 5 : ℝ) = p02 / ρ02 ^ (7 / 5 : ℝ)) ∧
    p01 < p02 ∧
      specificEntropyChange (1 / (7 / 5 - 1)) 1 (5 / 7) (1 / (7 / 5)) (5 / 16)
        (1 / (2 / 5)) < 0 := by
  obtain ⟨ρ01, p01, T01, hen1, hρ01, hp01, hs1⟩ := exists_isentropic_stagnation (γ := 7 / 5)
    (R := 1) (ρ := 7 / 5) (u := 1 / 2) (p := 1) (T := 5 / 7) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨ρ02, p02, T02, hen2, hρ02, hp02, hs2⟩ := exists_isentropic_stagnation (γ := 7 / 5)
    (R := 1) (ρ := 2 / 5) (u := 7 / 4) (p := 1 / 8) (T := 5 / 16) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hsel := normalShock_totalPressure_selection (a1 := 1) (M1 := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) normalShock_fixture_expansion.1 (by norm_num) hen1 hen2 hρ01 hρ02
    hp01 hp02 hs1 hs2
  obtain ⟨-, -, hrise, hΔ⟩ := hsel.2 (by norm_num)
  exact ⟨ρ01, p01, T01, ρ02, p02, T02, ⟨hen1, hρ01, hp01, hs1⟩, ⟨hen2, hρ02, hp02, hs2⟩, hrise,
    hΔ⟩

end PhyslibExtTest.FluidDynamics.PerfectGasPorts
