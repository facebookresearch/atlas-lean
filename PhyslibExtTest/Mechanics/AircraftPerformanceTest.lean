/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.AircraftPerformance

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Mechanics.AircraftPerformance`

Rounded standard-atmosphere values for the isothermal layer above 11 km, in SI units: reference
density `0.3639 kg/m³` at the layer base, `g = 9.80665 m/s²`, `Rs = 287.05 J/(kg K)`,
`T = 216.65 K`, declared band `[0, 9000] m` above the base.

* the scale height lies between `6341 m` and `6342 m`;
* two admissible heights of the band give different positive densities;
* the same state in kilometres gives `10 ^ 9` times the density in `kg/m³`.

A light airplane in SI units: `W = 10000 N`, `ρ = 1.25 kg/m³`, `S = 16 m²`, `k = 0.04`, clean
`CD0 = 0.02`; a high-drag configuration has `CD0 = 0.08` and `CLmax = 1.2`.

* at `40 m/s` the parasite drag is `320 N` and the induced drag `250 N`, so the level-flight
  drag is `570 N`;
* the minimum drag of the clean airplane lies between `565 N` and `566 N`;
* in the high-drag configuration the minimum-drag speed lies below the stall speed, so stall
  excludes the algebraic minimizer.

Power required for the clean airplane, `a = 0.2 kg/m` and `b = 400000 N m²/s²`:

* the minimum-power speed lies between `28 m/s` and `29 m/s`, below the minimum-drag speed
  between `37 m/s` and `38 m/s`;
* with `CLmax = 1.2` the minimum-power speed lies below the stall speed, so the least admissible
  power is at the stall endpoint;
* at `40 m/s` the power required is `22800 W`, from the formula and from the polar, it rises
  with speed there, and a propulsive efficiency `0.8` turns it into `28500 W` of shaft power.
-/

@[expose] public section

namespace PhyslibExtTest.Mechanics.AircraftPerformance

open _root_.AircraftPerformance

-- The scale height of the fixture layer lies between `6341 m` and `6342 m`.
example :
    6341 < scaleHeight 287.05 216.65 9.80665 ∧ scaleHeight 287.05 216.65 9.80665 < 6342 := by
  have h9 : (0:ℝ) < 9.80665 := by norm_num
  unfold scaleHeight
  rw [abs_of_pos h9]
  constructor
  · rw [lt_div_iff₀ h9]
    norm_num
  · rw [div_lt_iff₀ h9]
    norm_num

-- Two admissible heights of the band give different positive densities.
example :
    (0 : ℝ) ∈ Set.Icc (0 : ℝ) 9000 ∧ (1000 : ℝ) ∈ Set.Icc (0 : ℝ) 9000 ∧
      0 < isothermalDensity 0.3639 9.80665 287.05 216.65 1000 ∧
      isothermalDensity 0.3639 9.80665 287.05 216.65 1000 <
        isothermalDensity 0.3639 9.80665 287.05 216.65 0 := by
  have hρ : (0:ℝ) < 0.3639 := by norm_num
  have hg : (0:ℝ) < 9.80665 := by norm_num
  have hRs : (0:ℝ) < 287.05 := by norm_num
  have hT : (0:ℝ) < 216.65 := by norm_num
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 9000 := ⟨by norm_num, by norm_num⟩
  have h1000 : (1000:ℝ) ∈ Set.Icc (0:ℝ) 9000 := ⟨by norm_num, by norm_num⟩
  have hlt : (0:ℝ) < 1000 := by norm_num
  refine ⟨h0, h1000, isothermalDensity_pos hρ hRs hT _ _, ?_⟩
  exact isothermalDensity_strictAntiOn hρ hg hRs hT _ _ h0 h1000 hlt

-- The same state in kilometres (`l = 1 / 1000`): `ρ0 = 363900000 kg/km³`,
-- `g = 0.00980665 km/s²`, `Rs = 0.00028705 km²/(s² K)` and height `1 km` give `10 ^ 9` times
-- the density in `kg/m³` at `1000 m`.
example :
    isothermalDensity 363900000 0.00980665 0.00028705 216.65 1 =
      10 ^ 9 * isothermalDensity 0.3639 9.80665 287.05 216.65 1000 := by
  have h := isothermalDensity_unitChange (1:ℝ) (l := 1/1000) (s := 1) (k := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (show (0:ℝ) < 287.05 by norm_num) (show (0:ℝ) < 216.65 by norm_num)
    0.3639 9.80665 1000
  have e6 : ((1:ℝ) / (1/1000) ^ 3) = 10 ^ 9 := by norm_num
  have e1 : ((10:ℝ) ^ 9 * 0.3639) = 363900000 := by norm_num
  have e2 : ((1/1000:ℝ) / 1 ^ 2 * 9.80665) = 0.00980665 := by norm_num
  have e3 : ((1/1000:ℝ) ^ 2 / (1 ^ 2 * 1) * 287.05) = 0.00028705 := by norm_num
  have e4 : ((1:ℝ) * 216.65) = 216.65 := by norm_num
  have e5 : ((1/1000:ℝ) * 1000) = 1 := by norm_num
  rw [e6, e1, e2, e3, e4, e5] at h
  exact h

-- Nonzero weight and two positive drag contributions: at `V = 40 m/s` the parasite drag is
-- `320 N`, the induced drag `250 N`, the level-flight drag `570 N`.
example :
    parasiteDragFactor 1.25 16 0.02 * 40 ^ 2 = 320 ∧
      inducedDragFactor 10000 1.25 16 0.04 / 40 ^ 2 = 250 ∧
      levelDrag 10000 1.25 16 0.02 0.04 40 = 570 := by
  constructor
  · unfold parasiteDragFactor; norm_num
  · constructor
    · unfold inducedDragFactor; norm_num
    · unfold levelDrag parasiteDragFactor inducedDragFactor; norm_num

-- The minimum drag of the clean airplane lies between `565 N` and `566 N`
-- (`2 * W * √(CD0 * k) = 20000 * √0.0008 ≈ 565.7 N`), below the `570 N` at `40 m/s`.
example :
    565 < 2 * Real.sqrt (parasiteDragFactor 1.25 16 0.02 * inducedDragFactor 10000 1.25 16 0.04) ∧
      2 * Real.sqrt (parasiteDragFactor 1.25 16 0.02 * inducedDragFactor 10000 1.25 16 0.04) <
        566 := by
  have hab : parasiteDragFactor 1.25 16 0.02 * inducedDragFactor 10000 1.25 16 0.04
      = 80000 := by
    unfold parasiteDragFactor inducedDragFactor
    norm_num
  rw [hab]
  constructor
  · have h2 : (282.5 : ℝ) < Real.sqrt 80000 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    linarith [h2]
  · have h2 : Real.sqrt (80000 : ℝ) < 283 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    linarith [h2]

-- Stall can exclude the algebraic minimizer: in the high-drag configuration the minimum-drag
-- speed (about `26.6 m/s`) lies below the stall speed (about `28.9 m/s`).
example :
    minDragSpeed 10000 1.25 16 0.08 0.04 < stallSpeed 10000 1.25 16 1.2 := by
  have hiff := minDragSpeed_lt_stallSpeed_iff (W := 10000) (ρ := 1.25) (S := 16) (CD0 := 0.08)
    (k := 0.04) (CLmax := 1.2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [hiff]
  rw [show (0.08 / 0.04 : ℝ) = 2 by norm_num, Real.lt_sqrt (by norm_num)]
  norm_num

/-! ### Power required -/

-- Nonzero `a = 0.2 kg/m` and `b = 400000 N m²/s²` give different optimal speeds: the
-- minimum-power speed lies between `28 m/s` and `29 m/s` (`V_mp ^ 4 = 2000000 / 3`), the
-- minimum-drag speed between `37 m/s` and `38 m/s` (`V_md ^ 4 = 2000000`).
example :
    parasiteDragFactor 1.25 16 0.02 = 0.2 ∧ inducedDragFactor 10000 1.25 16 0.04 = 400000 ∧
      28 < minPowerSpeed 10000 1.25 16 0.02 0.04 ∧ minPowerSpeed 10000 1.25 16 0.02 0.04 < 29 ∧
      37 < minDragSpeed 10000 1.25 16 0.02 0.04 ∧ minDragSpeed 10000 1.25 16 0.02 0.04 < 38 := by
  have ha : parasiteDragFactor 1.25 16 0.02 = 0.2 := by unfold parasiteDragFactor; norm_num
  have hb : inducedDragFactor 10000 1.25 16 0.04 = 400000 := by
    unfold inducedDragFactor; norm_num
  have hW0 : (10000 : ℝ) ≠ 0 := by norm_num
  have hρ : (0 : ℝ) < 1.25 := by norm_num
  have hS : (0 : ℝ) < 16 := by norm_num
  have hCD0 : (0 : ℝ) < 0.02 := by norm_num
  have hk : (0 : ℝ) < 0.04 := by norm_num
  have hmp4 : minPowerSpeed 10000 1.25 16 0.02 0.04 ^ 4 = 2000000 / 3 := by
    have h := minPowerSpeed_pow_four hW0 hρ hS hCD0 hk
    rw [ha, hb] at h
    have h2 : (400000 : ℝ) / (3 * 0.2) = 2000000 / 3 := by norm_num
    rw [h2] at h
    exact h
  have hmd4 : minDragSpeed 10000 1.25 16 0.02 0.04 ^ 4 = 2000000 := by
    have h := minDragSpeed_pow_four hW0 hρ hS hCD0 hk
    rw [ha, hb] at h
    have h2 : (400000 : ℝ) / 0.2 = 2000000 := by norm_num
    rw [h2] at h
    exact h
  have hmp_pos := minPowerSpeed_pos hW0 hρ hS hCD0 hk
  have hmd_pos := minDragSpeed_pos hW0 hρ hS hCD0 hk
  have h4 : (4 : ℕ) ≠ 0 := by norm_num
  have hlo : 28 < minPowerSpeed 10000 1.25 16 0.02 0.04 := by
    have h28 : (28 : ℝ) ^ 4 < minPowerSpeed 10000 1.25 16 0.02 0.04 ^ 4 := by
      rw [hmp4]
      norm_num
    exact (pow_lt_pow_iff_left₀ (by norm_num) hmp_pos.le h4).mp h28
  have hhi : minPowerSpeed 10000 1.25 16 0.02 0.04 < 29 := by
    have h29 : minPowerSpeed 10000 1.25 16 0.02 0.04 ^ 4 < (29 : ℝ) ^ 4 := by
      rw [hmp4]
      norm_num
    exact (pow_lt_pow_iff_left₀ hmp_pos.le (by norm_num) h4).mp h29
  have hlo' : 37 < minDragSpeed 10000 1.25 16 0.02 0.04 := by
    have h37 : (37 : ℝ) ^ 4 < minDragSpeed 10000 1.25 16 0.02 0.04 ^ 4 := by
      rw [hmd4]
      norm_num
    exact (pow_lt_pow_iff_left₀ (by norm_num) hmd_pos.le h4).mp h37
  have hhi' : minDragSpeed 10000 1.25 16 0.02 0.04 < 38 := by
    have h38 : minDragSpeed 10000 1.25 16 0.02 0.04 ^ 4 < (38 : ℝ) ^ 4 := by
      rw [hmd4]
      norm_num
    exact (pow_lt_pow_iff_left₀ hmd_pos.le (by norm_num) h4).mp h38
  exact ⟨ha, hb, hlo, hhi, hlo', hhi'⟩

-- An invalid speed interval requires endpoint selection: the minimum-power speed (about
-- `28.57 m/s`, lift coefficient `√1.5 > 1.2`) lies below the stall speed (about `28.87 m/s`), so
-- the least admissible power is at the stall endpoint.
example :
    minPowerSpeed 10000 1.25 16 0.02 0.04 < stallSpeed 10000 1.25 16 1.2 ∧
      IsLeast (levelPower 10000 1.25 16 0.02 0.04 ''
          {V | 0 < V ∧ levelLiftCoeff 10000 1.25 16 V ≤ 1.2})
        (levelPower 10000 1.25 16 0.02 0.04 (stallSpeed 10000 1.25 16 1.2)) := by
  have hW : (0 : ℝ) < 10000 := by norm_num
  have hρ : (0 : ℝ) < 1.25 := by norm_num
  have hS : (0 : ℝ) < 16 := by norm_num
  have hCD0 : (0 : ℝ) < 0.02 := by norm_num
  have hk : (0 : ℝ) < 0.04 := by norm_num
  have hCL : (0 : ℝ) < 1.2 := by norm_num
  have hlt : minPowerSpeed 10000 1.25 16 0.02 0.04 < stallSpeed 10000 1.25 16 1.2 := by
    rw [minPowerSpeed_lt_stallSpeed_iff hW hρ hS hCD0 hk hCL]
    have h32 : (3 : ℝ) * 0.02 / 0.04 = 1.5 := by norm_num
    rw [h32]
    have hsq : (1.2 : ℝ) ^ 2 < 1.5 := by norm_num
    have h := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1.2 ^ 2 by positivity) hsq
    rw [Real.sqrt_sq (show (0 : ℝ) ≤ 1.2 by norm_num)] at h
    exact h
  have hleast := isLeast_levelPower_stall hW hρ hS hCD0 hk hCL
  rw [max_eq_left hlt.le] at hleast
  exact ⟨hlt, hleast⟩

private lemma minPowerSpeed_fixture_pow_four :
    minPowerSpeed 10000 1.25 16 0.02 0.04 ^ 4 = 2000000 / 3 := by
  rw [minPowerSpeed_pow_four (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  unfold parasiteDragFactor inducedDragFactor
  norm_num

private lemma minPowerSpeed_fixture_pos : 0 < minPowerSpeed 10000 1.25 16 0.02 0.04 :=
  minPowerSpeed_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private lemma minPowerSpeed_fixture_bounds :
    25 < minPowerSpeed 10000 1.25 16 0.02 0.04 ∧ minPowerSpeed 10000 1.25 16 0.02 0.04 < 30 := by
  have h4 : (4 : ℕ) ≠ 0 := by norm_num
  constructor
  · refine (pow_lt_pow_iff_left₀ (by norm_num) minPowerSpeed_fixture_pos.le h4).mp ?_
    rw [minPowerSpeed_fixture_pow_four]
    norm_num
  · refine (pow_lt_pow_iff_left₀ minPowerSpeed_fixture_pos.le (by norm_num) h4).mp ?_
    rw [minPowerSpeed_fixture_pow_four]
    norm_num

-- At `40 m/s` the power required is `0.2 * 40 ^ 3 + 400000 / 40 = 22800 W`, the level-flight drag
-- `570 N` times the speed; the polar gives the same value at the level-flight lift coefficient
-- `0.625`.
example :
    levelPower 10000 1.25 16 0.02 0.04 40 = 22800 ∧
      polarDrag 1.25 16 0.02 0.04 0.625 40 * 40 = 22800 := by
  have hP : levelPower 10000 1.25 16 0.02 0.04 40 = 22800 := by
    rw [levelPower_eq]
    unfold parasiteDragFactor inducedDragFactor
    norm_num
  refine ⟨hP, ?_⟩
  rw [polarDrag_mul_eq_levelPower (W := 10000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num), hP]

-- Above the minimum-power speed the power rises with speed:
-- `P'(40) = 3 * 0.2 * 40 ^ 2 - 400000 / 40 ^ 2 = 710 W s/m`, and `40 m/s` is not a minimizer
-- (`40 ^ 4 ≠ 2000000 / 3`).
example :
    HasDerivAt (levelPower 10000 1.25 16 0.02 0.04) 710 40 ∧
      ¬ IsMinOn (levelPower 10000 1.25 16 0.02 0.04) (Set.Ioi 0) 40 := by
  constructor
  · convert hasDerivAt_levelPower (W := 10000) (ρ := 1.25) (S := 16) (CD0 := 0.02) (k := 0.04)
      (V := 40) (by norm_num) using 1
    unfold parasiteDragFactor inducedDragFactor
    norm_num
  · rw [isMinOn_levelPower_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    unfold parasiteDragFactor inducedDragFactor
    norm_num

-- The least power over positive speeds is `P(V_mp)`, attained only at `V_mp`: `40 m/s`, the
-- minimum-drag speed and any other positive speed need more.
example :
    IsLeast (levelPower 10000 1.25 16 0.02 0.04 '' Set.Ioi 0)
        (levelPower 10000 1.25 16 0.02 0.04 (minPowerSpeed 10000 1.25 16 0.02 0.04)) ∧
      levelPower 10000 1.25 16 0.02 0.04 (minPowerSpeed 10000 1.25 16 0.02 0.04) <
        levelPower 10000 1.25 16 0.02 0.04 40 ∧
      levelPower 10000 1.25 16 0.02 0.04 (minPowerSpeed 10000 1.25 16 0.02 0.04) <
        levelPower 10000 1.25 16 0.02 0.04 (minDragSpeed 10000 1.25 16 0.02 0.04) := by
  refine ⟨isLeast_levelPower (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num), levelPower_minPowerSpeed_lt (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ?_, levelPower_minPowerSpeed_lt_minDragSpeed
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  exact (minPowerSpeed_fixture_bounds.2.trans (by norm_num : (30 : ℝ) < 40)).ne'

-- The power falls on `(0, V_mp]` and rises on `[V_mp, ∞)`: `P(25) < P(20)` and `P(30) < P(40)`.
example :
    levelPower 10000 1.25 16 0.02 0.04 25 < levelPower 10000 1.25 16 0.02 0.04 20 ∧
      levelPower 10000 1.25 16 0.02 0.04 30 < levelPower 10000 1.25 16 0.02 0.04 40 := by
  obtain ⟨hlo, hhi⟩ := minPowerSpeed_fixture_bounds
  constructor
  · exact levelPower_strictAntiOn (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ⟨by norm_num, by linarith⟩ ⟨by norm_num, hlo.le⟩ (by norm_num)
  · exact levelPower_strictMonoOn (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (show minPowerSpeed 10000 1.25 16 0.02 0.04 ≤ 30 from hhi.le)
      (show minPowerSpeed 10000 1.25 16 0.02 0.04 ≤ 40 by linarith) (by norm_num)

-- The two optima differ: `V_md ^ 4 = 3 * V_mp ^ 4`, `V_mp < V_md`, and the lift coefficient at
-- `V_mp` is `√1.5 = √(3 * CD0 / k)`.
example :
    minDragSpeed 10000 1.25 16 0.02 0.04 ^ 4 = 3 * minPowerSpeed 10000 1.25 16 0.02 0.04 ^ 4 ∧
      minPowerSpeed 10000 1.25 16 0.02 0.04 < minDragSpeed 10000 1.25 16 0.02 0.04 ∧
      levelLiftCoeff 10000 1.25 16 (minPowerSpeed 10000 1.25 16 0.02 0.04) = Real.sqrt 1.5 := by
  refine ⟨minDragSpeed_pow_four_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num), minPowerSpeed_lt_minDragSpeed (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num), ?_⟩
  rw [levelLiftCoeff_minPowerSpeed (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  norm_num

-- On the stall-validity interval with `CLmax = 1.2` the stall endpoint needs less power than the
-- admissible `40 m/s` (lift coefficient `0.625`).
example :
    levelPower 10000 1.25 16 0.02 0.04 (stallSpeed 10000 1.25 16 1.2) <
      levelPower 10000 1.25 16 0.02 0.04 40 := by
  have hlt : minPowerSpeed 10000 1.25 16 0.02 0.04 < stallSpeed 10000 1.25 16 1.2 := by
    rw [minPowerSpeed_lt_stallSpeed_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), Real.lt_sqrt (by norm_num)]
    norm_num
  have hs : stallSpeed 10000 1.25 16 1.2 < 40 := by
    unfold stallSpeed
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h := levelPower_max_lt (W := 10000) (ρ := 1.25) (S := 16) (CD0 := 0.02) (k := 0.04)
    (CLmax := 1.2) (V := 40) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by unfold levelLiftCoeff; norm_num)
    (by rw [max_eq_left hlt.le]; exact hs.ne')
  rwa [max_eq_left hlt.le] at h

-- With a propulsive efficiency `η = 0.8` the shaft power at `40 m/s` is `28500 W`, not the
-- `22800 W` of power required, and the shaft power is still least at `V_mp`.
example :
    shaftPowerRequired 0.8 10000 1.25 16 0.02 0.04 40 = 28500 ∧
      shaftPowerRequired 0.8 10000 1.25 16 0.02 0.04 40 ≠ levelPower 10000 1.25 16 0.02 0.04 40 ∧
      IsMinOn (shaftPowerRequired 0.8 10000 1.25 16 0.02 0.04) (Set.Ioi 0)
        (minPowerSpeed 10000 1.25 16 0.02 0.04) := by
  have hP : levelPower 10000 1.25 16 0.02 0.04 40 = 22800 := by
    rw [levelPower_eq]
    unfold parasiteDragFactor inducedDragFactor
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · unfold shaftPowerRequired
    rw [hP]
    norm_num
  · rw [Ne, shaftPowerRequired_eq_levelPower_iff (by rw [hP]; norm_num)]
    norm_num
  · rw [isMinOn_shaftPowerRequired_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      minPowerSpeed_fixture_pos]
    exact minPowerSpeed_pow_four (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)

end PhyslibExtTest.Mechanics.AircraftPerformance
