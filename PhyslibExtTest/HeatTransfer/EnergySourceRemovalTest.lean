/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.HeatTransfer.EnergySourceRemoval
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Slab, cylinder and coolant-channel heat-removal checks

Concrete consumers of `PhyslibExt.HeatTransfer.EnergySourceRemoval`:
the numeric slab `Ts = Tb = 300`, `L = 2`, `k = 2`, `H = 8` with
midplane `302` and total outward removal `16`, the source-free
branch `H = 0`, the numeric heated cylinder with outward power
`32π`, and a coolant channel with a cosine power profile: a nonzero
heat and flow case with outlet `565 + 1920 / (11π) K`, blocked flow
(no steady profile, while the outlet formula returns `T_in`), and
zero heating (constant `T_in`).

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or library results are introduced here.

## iii. Table of contents

- A. Numeric slab with source
- B. Source-free branch
- C. Numeric heated cylinder
- D. Coolant channel with a cosine power profile

## iv. References

- `PhyslibExt.HeatTransfer.EnergySourceRemoval`
-/

/-- Outward fluxes for the numeric slab: left outward flux
`k * T'(0) = 8`, right outward flux `-k * T'(2) = 8`, sum `16 = H * L`. -/
example : 2 * HeatTransfer.slabGradient 300 300 2 2 8 0 = 8 ∧
    -(2 * HeatTransfer.slabGradient 300 300 2 2 8 2) = 8 ∧
      2 * HeatTransfer.slabGradient 300 300 2 2 8 0 -
        2 * HeatTransfer.slabGradient 300 300 2 2 8 2 = 8 * 2 := by
  refine ⟨by norm_num [HeatTransfer.slabGradient],
    by norm_num [HeatTransfer.slabGradient], ?_⟩
  have h := HeatTransfer.outwardFluxSum (Ts := 300) (Tb := 300) (L := 2)
    (k := 2) (H := 8) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Midplane temperature of the numeric slab: `302`. -/
example : HeatTransfer.slabTemperature 300 300 2 2 8 1 = 302 := by
  have h := HeatTransfer.slabTemperature_midplane (Ts := 300) (L := 2)
    (k := 2) (H := 8) (by norm_num)
  norm_num at h
  exact h

/-- Source cutoff: with `H = 0` and equal surfaces the steady profile is
the constant surface temperature (a steady branch, not a transient). -/
example (d : ℝ) : HeatTransfer.slabTemperature 300 300 2 2 0 d = 300 := by
  simp [HeatTransfer.slabTemperature]

/-- Numeric heated cylinder `Ts = 300`, `R = 2`, `k = 2`, `qvol = 8`:
center `304`, surface `300`, rise `4`, zero center gradient, and the
radial equation value `-4` at `r = 1`. -/
example : HeatTransfer.cylinderTemperature 300 2 2 8 0 = 304 ∧
    HeatTransfer.cylinderTemperature 300 2 2 8 2 = 300 ∧
      HeatTransfer.cylinderGradient 2 8 0 = 0 ∧
        (1 / (1 : ℝ)) * deriv (fun s : ℝ =>
          s * HeatTransfer.cylinderGradient 2 8 s) 1 = -4 := by
  refine ⟨by norm_num [HeatTransfer.cylinderTemperature],
    by norm_num [HeatTransfer.cylinderTemperature],
    HeatTransfer.cylinderGradient_zero 2 8, ?_⟩
  have h := HeatTransfer.cylinder_radial_equation (R := 2) (k := 2)
    (qvol := 8) (r := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  rw [show (1 : ℝ) / 1 = 1 from by norm_num, one_mul]
  norm_num at h
  exact h

/-- Outward power per unit length of the numeric cylinder:
`2πR * (-k * T'(R)) = 32π` at `R = 2`, `k = 2`, `qvol = 8`. -/
example : 2 * Real.pi * 2 * (-2 * HeatTransfer.cylinderGradient 2 8 2) =
    32 * Real.pi := by
  have h := HeatTransfer.cylinder_outwardPower (R := 2) (k := 2)
    (qvol := 8) (by norm_num)
  calc 2 * Real.pi * 2 * (-2 * HeatTransfer.cylinderGradient 2 8 2)
      = Real.pi * 2 ^ 2 * 8 := h
    _ = 32 * Real.pi := by ring

/-- The domain-correct surface balance at positive radius and
conductivity gives the same numeric value `32π`. -/
example : 2 * Real.pi * 2 * (-2 * HeatTransfer.cylinderGradient 2 8 2) =
    32 * Real.pi := by
  have h := HeatTransfer.cylinder_outwardPower_of_pos (R := 2) (k := 2)
    (qvol := 8) (by norm_num) (by norm_num)
  calc 2 * Real.pi * 2 * (-2 * HeatTransfer.cylinderGradient 2 8 2)
      = Real.pi * 2 ^ 2 * 8 := h
    _ = 32 * Real.pi := by ring

/-! ## D. Coolant channel with a cosine power profile -/

namespace PhyslibExtTest.HeatTransfer.EnergySourceRemoval

open _root_.HeatTransfer

/-- Nonzero heat and flow, in SI units: `q₀ = 40000 W/m`, `L = Lₑ = 3.6 m`, `ṁ = 0.3 kg/s`,
`cp = 5500 J/(kg K)`, `Tin = 565 K`, `h_film = 40000 W/(m² K)`, `P = 0.03 m`. The outlet is
`Tout = 565 + 1920 / (11 π) ≈ 620.6 K`, and the clad envelope `Tout + 100 / 3` is below
`654 K`. -/
lemma fixture_nonzero_heat_flow :
    coolantOutletTemp 0.3 5500 40000 3.6 3.6 565 = 565 + 1920 / (11 * Real.pi) ∧
      620 < coolantOutletTemp 0.3 5500 40000 3.6 3.6 565 ∧
      coolantOutletTemp 0.3 5500 40000 3.6 3.6 565 < 621 ∧
      coolantOutletTemp 0.3 5500 40000 3.6 3.6 565 + 40000 / (40000 * 0.03) < 654 := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hD1 : Real.pi * 0.3 * 5500 ≠ 0 :=
    ne_of_gt (by positivity : (0 : ℝ) < Real.pi * 0.3 * 5500)
  have hD2 : (11 : ℝ) * Real.pi ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 11 * Real.pi)
  have harg : Real.pi * 3.6 / (2 * 3.6) = Real.pi / 2 := by
    field_simp
  have heq : coolantOutletTemp 0.3 5500 40000 3.6 3.6 565 = 565 + 1920 / (11 * Real.pi) := by
    unfold coolantOutletTemp
    rw [harg, Real.sin_pi_div_two]
    field_simp
    ring
  have h11 : (0 : ℝ) < 11 * Real.pi := by positivity
  refine ⟨heq, ?_, ?_, ?_⟩
  · rw [heq, show (620 : ℝ) = 565 + 55 by norm_num]
    have h : (55 : ℝ) < 1920 / (11 * Real.pi) := by
      rw [lt_div_iff₀ h11]
      have hlt := Real.pi_lt_d2
      linarith
    linarith [h]
  · rw [heq, show (621 : ℝ) = 565 + 56 by norm_num]
    have h : 1920 / (11 * Real.pi) < (56 : ℝ) := by
      rw [div_lt_iff₀ h11]
      have hgt := Real.pi_gt_d2
      linarith
    linarith [h]
  · rw [heq]
    have hfilm : (40000 : ℝ) / (40000 * 0.03) = 100 / 3 := by norm_num
    rw [hfilm]
    have h : 1920 / (11 * Real.pi) < (167 / 3 : ℝ) := by
      rw [div_lt_iff₀ h11]
      have hgt := Real.pi_gt_d2
      linarith
    linarith [h]

/-- Blocked flow invalidates the steady denominator: with `ṁ = 0` and `q₀ > 0` no temperature
profile satisfies the steady balance on the heated length, while the outlet formula evaluates to
the junk value `Tin`. -/
lemma fixture_blocked_flow {cp q0 Le L Tin : ℝ} (hq0 : 0 < q0) (hL : 0 < L) :
    (¬ ∃ T : ℝ → ℝ, IsSteadyCoolantProfile 0 cp q0 Le L Tin T) ∧
      coolantOutletTemp 0 cp q0 Le L Tin = Tin := by
  constructor
  · rintro ⟨T, hTin, hbal⟩
    have h0mem : (0 : ℝ) ∈ Set.Icc (-(L / 2)) (L / 2) := ⟨by linarith, by linarith⟩
    obtain ⟨-, h0⟩ := hbal 0 h0mem
    simp [cosineLinearPower] at h0
    linarith
  · simp [coolantOutletTemp]

/-- `q₀ = 0` recovers the constant inlet temperature: every steady profile without heating is
`Tin` on the heated length, and so is the outlet. -/
lemma fixture_zero_heat {mdot cp Le L Tin : ℝ} {T : ℝ → ℝ} (hm : 0 < mdot) (hcp : 0 < cp)
    (hLe : 0 < Le) (hT : IsSteadyCoolantProfile mdot cp 0 Le L Tin T) :
    (∀ z ∈ Set.Icc (-(L / 2)) (L / 2), T z = Tin) ∧ coolantOutletTemp mdot cp 0 Le L Tin = Tin := by
  constructor
  · intro z hz
    have heq := IsSteadyCoolantProfile.eq_coolantTemperature hm hcp hLe hT z hz
    rw [heq]
    simp [coolantTemperature]
  · simp [coolantOutletTemp]

end PhyslibExtTest.HeatTransfer.EnergySourceRemoval
