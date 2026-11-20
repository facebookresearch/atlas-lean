/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import PhyslibExt.Thermodynamics.ExergyAndLosses

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for `PhyslibExt.Thermodynamics.ExergyAndLosses`

Two steady open systems in kW, kJ/kg, kJ/(kg K) and K, with `T₀ = 300 K`:

* a mixing chamber with heat loss whose supplied entropy production is `0.01 kW/K > 0`, so its
  destroyed exergy is `3 kW` for every dead-state enthalpy and entropy;
* a reverse throttle that satisfies the steady first law and the mass balance but has entropy
  generation `-0.4 kW/K` and destroyed exergy `-120 kW`: energy conservation alone does not
  establish the second law.

A lossy air-standard Brayton loop (`R = 287 J/(kg K)`, `cp = 2009/2 J/(kg K)`, pressure ratio
`(3/2) ^ 7`, so `a = 9/4`, from `300 K` to the turbine inlet `1350 K`, where the threshold
`a T₁ / T₃` is `1/2`):

* with compressor efficiency `5/6` and turbine efficiency `9/10` it does `452025/2 J/kg` of net
  work on the positive heat input `602700 J/kg`, with efficiency `3/8`, below the ideal `5/9`;
* with compressor efficiency `5/8` it still absorbs heat, but turbine efficiency `4/5`
  (`ηc ηt = 1/2`, the threshold) gives zero net work and `3/5` negative net work;
* with compressor efficiency `1/4` its heat input is negative, and the work-to-heat ratio, which
  is no efficiency there, falls from `5/2` to `5/3` as the turbine efficiency rises from `1/2`
  to `1`;
* every result of section C applies to it, including the threshold equality and the case below
  the threshold, where the work is negative.

A regenerated variant of the same loop (regenerator conductance `UA = 6027/2 J/(kg K)` per unit
mass flow, so `NTU = 3` and effectiveness `3/4`):

* at the turbine inlet `1800 K` the exhaust (`900 K`) is hotter than the compressed air
  (`750 K`): the regenerator recovers `452025/4 J/kg`, preheating the air to `1725/2 K` and
  cooling the exhaust to `1575/2 K`, and the external heat demand falls from `1054725 J/kg` to
  `3766875/4 J/kg` at unchanged work;
* at the turbine inlet `1350 K` the exhaust (`675 K`) is colder: the regenerator is bypassed and
  recovers nothing, where the effectiveness formula would give the negative `-452025/8 J/kg`, and
  a counterflow exchanger connected anyway would cool the compressed air;
* at the turbine inlet `1500 K` both are at `750 K`: the bypass recovers nothing and a connected
  exchanger moves no heat;
* every result of section D applies to it.
-/

@[expose] public section

namespace PhyslibExtTest.Thermodynamics.ExergyAndLosses

open _root_.ExergyAndLosses _root_.GasCycles

/-- A mixing chamber with heat loss (two inlets, one outlet, one heat port, no shaft work), in
kW, kJ/kg, kJ/(kg K) and K: liquid water at `1 kg/s` with `θ = 100`, `s = 0.35` and at
`1 kg/s` with `θ = 300`, `s = 0.98` leaves as `2 kg/s` with `θ = 197`, `s = 0.66`, losing
`6 kW` (`Q̇ = -6`) through a boundary at `300 K`, with `T₀ = 300 K`. The steady first law and
mass balance hold, the supplied entropy production is `0.01 kW/K > 0`, and the destroyed exergy
is `3 kW = T₀ Ṡ_gen` for every dead-state enthalpy and entropy. -/
lemma fixture_mixing_chamber (h0 s0 : ℝ) :
    energyResidual ![(-6 : ℝ)] 0 ![1, 1] ![100, 300] ![2] ![197] = 0 ∧
      ∑ i, (![1, 1] : Fin 2 → ℝ) i = ∑ o, (![2] : Fin 1 → ℝ) o ∧
      entropyGen ![(-6 : ℝ)] ![300] ![1, 1] ![0.35, 0.98] ![2] ![0.66] = 0.01 ∧
      exergyDestroyed 300 h0 s0 ![(-6 : ℝ)] ![300] 0 ![1, 1] ![100, 300] ![0.35, 0.98]
        ![2] ![197] ![0.66] = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold energyResidual ProcessPorts.workOut
    simp [Fin.sum_univ_two]
    norm_num
  · simp [Fin.sum_univ_two]
    norm_num
  · unfold entropyGen
    simp [Fin.sum_univ_two]
    norm_num
  · unfold exergyDestroyed flowExergy ProcessPorts.workOut
    simp [Fin.sum_univ_two]
    ring

/-- Energy conservation alone does not establish the second law: an adiabatic, workless
reverse throttle of air (`2 kg/s`, `θ = 300 kJ/kg` in and out, `s` falling from `1.9` to
`1.7 kJ/(kg K)`, as for a pressure rise from `100 kPa` to `200 kPa` at `300 K`) satisfies the
steady first law and the mass balance, yet its entropy generation is `-0.4 kW/K` and its
destroyed exergy is `-120 kW` at `T₀ = 300 K`. -/
lemma fixture_energy_without_second_law (h0 s0 : ℝ) :
    energyResidual (![] : Fin 0 → ℝ) 0 ![(2 : ℝ)] ![300] ![(2 : ℝ)] ![300] = 0 ∧
      ∑ i, (![2] : Fin 1 → ℝ) i = ∑ o, (![2] : Fin 1 → ℝ) o ∧
      entropyGen (![] : Fin 0 → ℝ) ![] ![(2 : ℝ)] ![1.9] ![(2 : ℝ)] ![1.7] = -0.4 ∧
      exergyDestroyed 300 h0 s0 (![] : Fin 0 → ℝ) ![] 0 ![(2 : ℝ)] ![300] ![1.9] ![(2 : ℝ)]
        ![300] ![1.7] = -120 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold energyResidual ProcessPorts.workOut
    simp
  · simp
  · unfold entropyGen
    simp
    norm_num
  · unfold exergyDestroyed flowExergy ProcessPorts.workOut
    simp
    ring

/-! ## Nonideal Brayton cycle -/

/-- The air-standard ratio `a = ((3/2) ^ 7) ^ (2/7) = 9/4` of the Brayton fixtures. -/
private lemma braytonTempRatio_air : braytonTempRatio (2187 / 128) 287 (2009 / 2) = 9 / 4 := by
  rw [braytonTempRatio, show (2187 / 128 : ℝ) = (3 / 2) ^ (7 : ℕ) by norm_num,
    show (287 : ℝ) / (2009 / 2) = 2 / 7 by norm_num, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)]
  norm_num

/-- **Fixture: a lossy air loop with positive work.** Air with `R = 287 J/(kg K)` and
`cp = 2009/2 J/(kg K)` (`R / cp = 2/7`, `γ = 7/5`) at pressure ratio `rp = (3/2) ^ 7 = 2187/128`,
so `a = 9/4`, from `T₁ = 300 K` to the turbine inlet `T₃ = 1350 K`, with compressor efficiency
`5/6` and turbine efficiency `9/10`: the threshold `a T₁ / T₃ = 1/2` lies below `ηc ηt = 3/4`;
`T₂ = 750 K` (isentropic `675 K`) and `T₄ = 675 K` (isentropic `600 K`); per unit mass
`Qin = 602700 J/kg`, `Qout = 753375/2 J/kg` and `Wnet = 452025/2 J/kg`; and `η = 3/8`, below the
ideal `5/9`. -/
lemma braytonLossy_fixture_air :
    braytonTempRatio (2187 / 128) 287 (2009 / 2) * 300 / 1350 = 1 / 2 ∧
      braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) = 750 ∧
      braytonLossyExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) (9 / 10) = 675 ∧
      braytonLossyHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) = 602700 ∧
      braytonLossyHeatOut 300 1350 (2187 / 128) 287 (2009 / 2) (9 / 10) = 753375 / 2 ∧
      braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) = 452025 / 2 ∧
      braytonLossyEfficiency 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) = 3 / 8 ∧
      braytonEfficiency (2187 / 128) 287 (2009 / 2) = 5 / 9 := by
  have ha := braytonTempRatio_air
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha]
    norm_num
  · simp only [braytonLossyCompressedTemp, ha]
    norm_num
  · simp only [braytonLossyExpandedTemp, ha]
    norm_num
  · simp only [braytonLossyHeatIn, braytonLossyCompressedTemp, ha]
    norm_num
  · simp only [braytonLossyHeatOut, braytonLossyExpandedTemp, ha]
    norm_num
  · simp only [braytonLossyNetWork, braytonLossyCompressedTemp, braytonLossyExpandedTemp, ha]
    norm_num
  · simp only [braytonLossyEfficiency, braytonLossyNetWork, braytonLossyHeatIn,
      braytonLossyCompressedTemp, braytonLossyExpandedTemp, ha]
    norm_num
  · simp only [braytonEfficiency, ha]
    norm_num

/-- **Fixture: low efficiencies stop the work.** The same air loop with compressor efficiency
`5/8` reaches `T₂ = 900 K` and still absorbs `Qin = 452025 J/kg > 0`; with turbine efficiency
`4/5` (`ηc ηt = 1/2`, exactly the threshold `a T₁ / T₃`) its net work is zero, and with `3/5`
(`ηc ηt = 3/8`) it is `-150675 J/kg`. -/
lemma braytonLossy_fixture_lowEfficiency :
    braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 8) = 900 ∧
      braytonLossyHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 8) = 452025 ∧
      braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 8) (4 / 5) = 0 ∧
      braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 8) (3 / 5) = -150675 := by
  have ha := braytonTempRatio_air
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [braytonLossyCompressedTemp, ha]
    norm_num
  · simp only [braytonLossyHeatIn, braytonLossyCompressedTemp, ha]
    norm_num
  · simp only [braytonLossyNetWork, braytonLossyCompressedTemp, braytonLossyExpandedTemp, ha]
    norm_num
  · simp only [braytonLossyNetWork, braytonLossyCompressedTemp, braytonLossyExpandedTemp, ha]
    norm_num

/-- **Fixture: without positive heat input the comparison reverses.** With compressor efficiency
`1/4` the same air loop overshoots the turbine inlet, `T₂ = 1800 K > T₃`, so
`Qin = -452025 J/kg < 0`; raising the turbine efficiency from `1/2` to `1` then lowers the ratio
`Wnet / Qin` from `5/2` to `5/3`, the opposite of its rise on positive heat input. -/
lemma braytonLossy_fixture_heatIn_neg :
    braytonLossyHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) (1 / 4) = -452025 ∧
      braytonLossyEfficiency 300 1350 (2187 / 128) 287 (2009 / 2) (1 / 4) (1 / 2) = 5 / 2 ∧
      braytonLossyEfficiency 300 1350 (2187 / 128) 287 (2009 / 2) (1 / 4) 1 = 5 / 3 := by
  have ha := braytonTempRatio_air
  refine ⟨?_, ?_, ?_⟩
  · simp only [braytonLossyHeatIn, braytonLossyCompressedTemp, ha]
    norm_num
  · simp only [braytonLossyEfficiency, braytonLossyNetWork, braytonLossyHeatIn,
      braytonLossyCompressedTemp, braytonLossyExpandedTemp, ha]
    norm_num
  · simp only [braytonLossyEfficiency, braytonLossyNetWork, braytonLossyHeatIn,
      braytonLossyCompressedTemp, braytonLossyExpandedTemp, ha]
    norm_num

-- At efficiency one the air loop is the ideal one: net work `753375/2 J/kg`.
example : braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) 1 1 = 753375 / 2 := by
  rw [(braytonLossy_one 300 1350 (2187 / 128) 287 (2009 / 2)).2.2.2.2.1]
  simp only [braytonNetWork, braytonCompressedTemp, braytonExpandedTemp, braytonTempRatio_air]
  norm_num

-- The compressor efficiency `5/6` is the isentropic rise `375 K` over the actual rise `450 K`.
example : (braytonCompressedTemp 300 (2187 / 128) 287 (2009 / 2) - 300) /
    (braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) - 300) = 5 / 6 :=
  (braytonLossy_isentropicEfficiency (cp := 2009 / 2) (R := 287) (rp := 2187 / 128) (T₁ := 300)
    (T₃ := 1350) (ηc := 5 / 6) (ηt := 9 / 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).1.symm

-- Losses raise both exits: `675 K ≤ 750 K` at the compressor and `600 K ≤ 675 K` at the turbine.
example : braytonCompressedTemp 300 (2187 / 128) 287 (2009 / 2) ≤
      braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) ∧
    braytonExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) ≤
      braytonLossyExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) (9 / 10) := by
  have h := braytonLossy_temp_order (cp := 2009 / 2) (R := 287) (rp := 2187 / 128) (T₁ := 300)
    (T₃ := 1350) (ηc := 5 / 6) (ηt := 9 / 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.2.1, h.2.2.1⟩

-- The first law around the loop, `602700 - 753375/2 = 452025/2 J/kg`, and the closed form of the
-- work, `cp (5/9) (1215 - 810) = 452025/2 J/kg`.
example : braytonLossyHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) -
      braytonLossyHeatOut 300 1350 (2187 / 128) 287 (2009 / 2) (9 / 10) = 452025 / 2 ∧
    2009 / 2 * (1 - 1 / braytonTempRatio (2187 / 128) 287 (2009 / 2)) *
      (9 / 10 * 1350 - braytonTempRatio (2187 / 128) 287 (2009 / 2) * 300 / (5 / 6)) =
      452025 / 2 := by
  have h := braytonLossy_closed_loop (cp := 2009 / 2) (R := 287) (rp := 2187 / 128) (T₁ := 300)
    (T₃ := 1350) (ηc := 5 / 6) (ηt := 9 / 10) (by norm_num)
  rw [braytonLossy_fixture_air.2.2.2.2.2.1] at h
  exact ⟨h.1.symm, h.2.symm⟩

-- On positive heat input the efficiency `3/8` is `1 - Qout / Qin` and the closed form.
example : 1 - braytonLossyHeatOut 300 1350 (2187 / 128) 287 (2009 / 2) (9 / 10) /
      braytonLossyHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) = 3 / 8 ∧
    (1 - 1 / braytonTempRatio (2187 / 128) 287 (2009 / 2)) *
        (5 / 6 * (9 / 10) * 1350 - braytonTempRatio (2187 / 128) 287 (2009 / 2) * 300) /
      (5 / 6 * (1350 - 300) - (braytonTempRatio (2187 / 128) 287 (2009 / 2) - 1) * 300) =
      3 / 8 := by
  have h := braytonLossyEfficiency_eq (cp := 2009 / 2) (R := 287) (rp := 2187 / 128) (T₁ := 300)
    (T₃ := 1350) (ηc := 5 / 6) (ηt := 9 / 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [braytonLossy_fixture_air.2.1]; norm_num)
  rw [braytonLossy_fixture_air.2.2.2.2.2.2.1] at h
  exact ⟨h.1.symm, h.2.symm⟩

-- The compressor takes `2/3` of the turbine output.
example : 2009 / 2 * (braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) - 300) /
      (2009 / 2 * (1350 - braytonLossyExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) (9 / 10))) =
    2 / 3 := by
  rw [braytonLossy_backWorkRatio (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num), braytonTempRatio_air]
  norm_num

-- The threshold `a T₁ / T₃ = 1/2`: positive work at `ηc ηt = 3/4`, none at the threshold
-- `ηc ηt = 1/2` and none below it at `ηc ηt = 3/8`.
example : 0 < braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) ∧
    ¬ 0 < braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 8) (4 / 5) ∧
    ¬ 0 < braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 8) (3 / 5) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [braytonLossyNetWork_pos_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), braytonLossy_fixture_air.1] <;>
    norm_num

-- Threshold equality gives zero work.
example : braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 8) (4 / 5) = 0 := by
  rw [braytonLossyNetWork_eq_zero_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num), braytonLossy_fixture_air.1]
  norm_num

-- Below the threshold the work is negative: not positive and not zero.
example : braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 8) (3 / 5) < 0 := by
  have hpos : ¬ 0 < braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 8) (3 / 5) := by
    rw [braytonLossyNetWork_pos_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), braytonLossy_fixture_air.1]
    norm_num
  have hne : braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 8) (3 / 5) ≠ 0 := by
    rw [ne_eq, braytonLossyNetWork_eq_zero_iff (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), braytonLossy_fixture_air.1]
    norm_num
  exact lt_of_le_of_ne (not_lt.mp hpos) hne

-- More efficient compression gives more work, as `ηc` rises from `5/8` to `5/6`.
example : braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 8) (9 / 10) <
    braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) := by
  exact braytonLossyNetWork_strictMonoOn_compressorEff (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- More efficient expansion gives more work, `-150675 < 0 J/kg` as `ηt` rises from `3/5` to `4/5`.
example : braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 8) (3 / 5) <
    braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 8) (4 / 5) := by
  exact braytonLossyNetWork_strictMonoOn_turbineEff (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- On positive heat input the efficiency rises with `ηc`, from `1/6` at `5/8` to `3/8` at `5/6`.
example : braytonLossyEfficiency 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 8) (9 / 10) <
    braytonLossyEfficiency 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) := by
  have hm₁ : (5 / 8 : ℝ) ∈ Set.Ioc 0 1 ∩
      {ηc | braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) ηc < 1350} := by
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    change braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 8) < 1350
    rw [braytonLossy_fixture_lowEfficiency.1]
    norm_num
  have hm₂ : (5 / 6 : ℝ) ∈ Set.Ioc 0 1 ∩
      {ηc | braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) ηc < 1350} := by
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    change braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) < 1350
    rw [braytonLossy_fixture_air.2.1]
    norm_num
  exact braytonLossyEfficiency_strictMonoOn_compressorEff (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hm₁ hm₂ (by norm_num)

-- On positive heat input (`T₂ = 900 K`) the efficiency rises with `ηt`, from `-1/3` to `0`.
example : braytonLossyEfficiency 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 8) (3 / 5) <
    braytonLossyEfficiency 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 8) (4 / 5) := by
  have hT : braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 8) < 1350 := by
    rw [braytonLossy_fixture_lowEfficiency.1]
    norm_num
  exact braytonLossyEfficiency_strictMonoOn_turbineEff (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hT (by norm_num) (by norm_num) (by norm_num)

-- Losses lower the efficiency: on positive heat input `3/8 < 5/9`, strictly since `ηc ≠ 1`; at
-- `ηc = ηt = 1` it is the ideal one.
example : braytonLossyEfficiency 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) <
      braytonEfficiency (2187 / 128) 287 (2009 / 2) ∧
    braytonLossyEfficiency 300 1350 (2187 / 128) 287 (2009 / 2) 1 1 =
      braytonEfficiency (2187 / 128) 287 (2009 / 2) := by
  have h := braytonLossyEfficiency_le_braytonEfficiency (cp := 2009 / 2) (R := 287)
    (rp := 2187 / 128) (T₁ := 300) (T₃ := 1350) (ηc := 5 / 6) (ηt := 9 / 10) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [braytonLossy_fixture_air.2.1]; norm_num)
  have h₁ := braytonLossyEfficiency_le_braytonEfficiency (cp := 2009 / 2) (R := 287)
    (rp := 2187 / 128) (T₁ := 300) (T₃ := 1350) (ηc := 1) (ηt := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [(braytonLossy_one 300 1350 (2187 / 128) 287 (2009 / 2)).1, braytonCompressedTemp,
      braytonTempRatio_air]; norm_num)
  refine ⟨lt_of_le_of_ne h.1 fun heq => ?_, h₁.2.mpr ⟨rfl, rfl⟩⟩
  have h₂ := (h.2.mp heq).1
  norm_num at h₂

/-! ## Regeneration -/

open _root_.HeatTransfer.HeatExchangers

/-- **Fixture: nonzero recoverable heat.** The air loop of section C (`R = 287 J/(kg K)`,
`cp = 2009/2 J/(kg K)`, `rp = 2187/128`, so `a = 9/4`, `T₁ = 300 K`, `ηc = 5/6`, `ηt = 9/10`) with
the hotter turbine inlet `T₃ = 1800 K` has `T₂ = 750 K < T₄ = 900 K`. A regenerator with
`UA = 6027/2 J/(kg K)` per unit mass flow (`NTU = 3`) has `ε = 3/4`: the compressed stream leaves
it at `T₅ = 1725/2 K`, the exhaust at `T₆ = 1575/2 K` (a temperature cross), the recovered heat
is `Q_reg = 452025/4 J/kg`, and the external heat demand falls from `Qin = 1054725 J/kg` to
`Qin_reg = 3766875/4 J/kg`. -/
lemma braytonRegen_fixture_recovery :
    braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) = 750 ∧
      braytonLossyExpandedTemp 1800 (2187 / 128) 287 (2009 / 2) (9 / 10) = 900 ∧
      counterflowEffectiveness (transferUnits (6027 / 2) (2009 / 2) (2009 / 2))
        (capacityRatio (2009 / 2) (2009 / 2)) = 3 / 4 ∧
      braytonRegenPreheatTemp 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) =
        1725 / 2 ∧
      braytonRegenExhaustTemp 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) =
        1575 / 2 ∧
      braytonRegenHeat 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) =
        452025 / 4 ∧
      braytonLossyHeatIn 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) = 1054725 ∧
      braytonRegenHeatIn 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) =
        3766875 / 4 := by
  have ha := braytonTempRatio_air
  have hA : braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) = 750 := by
    simp only [braytonLossyCompressedTemp, ha]
    norm_num
  have hB : braytonLossyExpandedTemp 1800 (2187 / 128) 287 (2009 / 2) (9 / 10) = 900 := by
    simp only [braytonLossyExpandedTemp, ha]
    norm_num
  have hE : counterflowEffectiveness (transferUnits (6027 / 2) (2009 / 2) (2009 / 2))
      (capacityRatio (2009 / 2) (2009 / 2)) = 3 / 4 := by
    rw [(braytonRegen_effectiveness (cp := 2009 / 2) (UA := 6027 / 2) (by norm_num)
      (by norm_num)).2.2.1]
    norm_num
  have hT : braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) <
      braytonLossyExpandedTemp 1800 (2187 / 128) 287 (2009 / 2) (9 / 10) := by
    rw [hA, hB]
    norm_num
  obtain ⟨h5, h6, -⟩ := braytonRegen_of_lt (UA := 6027 / 2) hT
  rw [hA, hB, hE] at h5 h6
  refine ⟨hA, hB, hE, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h5]
    norm_num
  · rw [h6]
    norm_num
  · rw [braytonRegenHeat, h5, hA]
    norm_num
  · simp only [braytonLossyHeatIn, hA]
    norm_num
  · rw [braytonRegenHeatIn, h5]
    norm_num

/-- **Fixture: a colder exhaust takes the bypass, not a negative recovery.** The air loop of
section C at its own turbine inlet `T₃ = 1350 K` has `T₄ = 675 K < T₂ = 750 K`. The same
regenerator is bypassed: it recovers `Q_reg = 0` and the external heat demand stays
`Qin = 602700 J/kg`, whereas the effectiveness contract applied against the gradient,
`ε Cmin (T₄ - T₂)`, would give the negative `-452025/8 J/kg`. -/
lemma braytonRegen_fixture_bypass :
    braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) = 750 ∧
      braytonLossyExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) (9 / 10) = 675 ∧
      braytonRegenHeat 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) = 0 ∧
      braytonRegenHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) =
        602700 ∧
      braytonLossyHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) = 602700 ∧
      counterflowEffectiveness (transferUnits (6027 / 2) (2009 / 2) (2009 / 2))
          (capacityRatio (2009 / 2) (2009 / 2)) * min (2009 / 2) (2009 / 2) *
        (braytonLossyExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) (9 / 10) -
          braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6)) = -452025 / 8 := by
  have ha := braytonTempRatio_air
  have hA : braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) = 750 := by
    simp only [braytonLossyCompressedTemp, ha]
    norm_num
  have hB : braytonLossyExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) (9 / 10) = 675 := by
    simp only [braytonLossyExpandedTemp, ha]
    norm_num
  have hE : counterflowEffectiveness (transferUnits (6027 / 2) (2009 / 2) (2009 / 2))
      (capacityRatio (2009 / 2) (2009 / 2)) = 3 / 4 := by
    rw [(braytonRegen_effectiveness (cp := 2009 / 2) (UA := 6027 / 2) (by norm_num)
      (by norm_num)).2.2.1]
    norm_num
  have hT : braytonLossyExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) (9 / 10) ≤
      braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) := by
    rw [hA, hB]
    norm_num
  obtain ⟨-, -, hQ, hQin, -⟩ := braytonRegen_bypass (UA := 6027 / 2) hT
  have hQin0 : braytonLossyHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) = 602700 := by
    simp only [braytonLossyHeatIn, hA]
    norm_num
  refine ⟨hA, hB, hQ, hQin.trans hQin0, hQin0, ?_⟩
  rw [hE, hA, hB, min_self]
  norm_num


/-- The recovery fixture's exhaust is hotter than its compressed stream, `750 K < 900 K`. -/
private lemma regen_recovery_lt :
    braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) <
      braytonLossyExpandedTemp 1800 (2187 / 128) 287 (2009 / 2) (9 / 10) := by
  rw [braytonRegen_fixture_recovery.1, braytonRegen_fixture_recovery.2.1]
  norm_num

/-- The bypass fixture's exhaust is colder than its compressed stream, `675 K < 750 K`. -/
private lemma regen_bypass_lt :
    braytonLossyExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) (9 / 10) <
      braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) := by
  rw [braytonRegen_fixture_bypass.1, braytonRegen_fixture_bypass.2.1]
  norm_num

-- The regenerator of the fixtures runs at `Cr = 1` with `NTU = 3`.
example : capacityRatio (2009 / 2) (2009 / 2) = 1 ∧
    transferUnits (6027 / 2) (2009 / 2) (2009 / 2) = 3 := by
  obtain ⟨hCr, hN, -, -, -⟩ := braytonRegen_effectiveness (cp := 2009 / 2) (UA := 6027 / 2)
    (by norm_num) (by norm_num)
  refine ⟨hCr, ?_⟩
  rw [hN]
  norm_num

-- Exhaust hotter: the recovered heat is the contract `ε Cmin (T₄ - T₂) = (3/4) cp 150 J/kg`.
example : braytonRegenHeat 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) =
    3 / 4 * min (2009 / 2) (2009 / 2) * (900 - 750) := by
  rw [(braytonRegen_of_lt (UA := 6027 / 2) regen_recovery_lt).2.2,
    braytonRegen_fixture_recovery.2.2.1, braytonRegen_fixture_recovery.1,
    braytonRegen_fixture_recovery.2.1]

-- Exhaust colder: the bypass passes both streams unchanged and keeps the work-to-heat ratio
-- `3/8` of the loop without regenerator.
example :
    braytonRegenPreheatTemp 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) =
        750 ∧
      braytonRegenExhaustTemp 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) =
        675 ∧
      braytonLossyNetWork 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) /
          braytonRegenHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) =
        3 / 8 := by
  obtain ⟨h5, h6, -, -, hr⟩ := braytonRegen_bypass (UA := 6027 / 2) regen_bypass_lt.le
  refine ⟨?_, ?_, ?_⟩
  · rw [h5, braytonRegen_fixture_bypass.1]
  · rw [h6, braytonRegen_fixture_bypass.2.1]
  · rw [hr, braytonLossy_fixture_air.2.2.2.2.2.2.1]

-- Equal temperatures, `T₂ = T₄ = 750 K` at the turbine inlet `1500 K`: the bypass recovers no
-- heat, the demand is unchanged, and no positive recovery is possible there.
example : braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) =
      braytonLossyExpandedTemp 1500 (2187 / 128) 287 (2009 / 2) (9 / 10) ∧
    braytonRegenHeat 300 1500 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) = 0 ∧
    braytonRegenHeatIn 300 1500 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) =
      braytonLossyHeatIn 300 1500 (2187 / 128) 287 (2009 / 2) (5 / 6) ∧
    ¬ 0 < braytonRegenHeat 300 1500 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) := by
  have ha := braytonTempRatio_air
  have hA : braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) = 750 := by
    simp only [braytonLossyCompressedTemp, ha]
    norm_num
  have hB : braytonLossyExpandedTemp 1500 (2187 / 128) 287 (2009 / 2) (9 / 10) = 750 := by
    simp only [braytonLossyExpandedTemp, ha]
    norm_num
  have heq := hA.trans hB.symm
  obtain ⟨-, -, hQ, hQin, -⟩ := braytonRegen_bypass (UA := 6027 / 2) heq.symm.le
  refine ⟨heq, hQ, hQin, fun h => ?_⟩
  have hlt := ((braytonRegenHeat_pos_iff (by norm_num) (by norm_num)).mp h).1
  rw [heq] at hlt
  exact lt_irrefl _ hlt

-- Equal temperatures: a counterflow exchanger connected between the ports moves no heat either.
example :
    2009 / 2 * (counterflowColdTemp (2009 / 2) (2009 / 2) (6027 / 2 / 1) 1
        (braytonLossyExpandedTemp 1500 (2187 / 128) 287 (2009 / 2) (9 / 10))
        (braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6)) 0 -
      braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6)) = 0 ∧
    2009 / 2 * (braytonLossyExpandedTemp 1500 (2187 / 128) 287 (2009 / 2) (9 / 10) -
      counterflowHotTemp (2009 / 2) (2009 / 2) (6027 / 2 / 1) 1
        (braytonLossyExpandedTemp 1500 (2187 / 128) 287 (2009 / 2) (9 / 10))
        (braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6)) 1) = 0 := by
  have ha := braytonTempRatio_air
  have hAB : braytonLossyExpandedTemp 1500 (2187 / 128) 287 (2009 / 2) (9 / 10) -
      braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) = 0 := by
    simp only [braytonLossyExpandedTemp, braytonLossyCompressedTemp, ha]
    norm_num
  have hsol := isCounterflowSolution_closedForm (Ch := 2009 / 2) (Cc := 2009 / 2)
    (K := 6027 / 2 / 1) (L := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (braytonLossyExpandedTemp 1500 (2187 / 128) 287 (2009 / 2) (9 / 10))
    (braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6))
  obtain ⟨hhot, hcold⟩ := hsol.heat_eq_effectiveness (UA := 6027 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  rw [hAB, mul_zero] at hhot hcold
  exact ⟨hcold, hhot⟩

-- Heat balance at the recovery fixture: the exhaust gives `cp (900 - 1575/2) = 452025/4 J/kg`, the
-- demand falls by it from `1054725 J/kg`, and the work `452025 J/kg` is the regenerated demand
-- less the heat rejected from `1575/2 K`.
example :
    2009 / 2 * (900 - 1575 / 2) =
        braytonRegenHeat 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) ∧
      braytonRegenHeatIn 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) =
        1054725 - 452025 / 4 ∧
      braytonLossyNetWork 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) =
        3766875 / 4 - 2009 / 2 * (1575 / 2 - 300) := by
  obtain ⟨h1, h2, h3⟩ :=
    braytonRegen_heat_balance 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2)
  rw [braytonRegen_fixture_recovery.2.1, braytonRegen_fixture_recovery.2.2.2.2.1] at h1
  rw [braytonRegen_fixture_recovery.2.2.2.2.2.2.1, braytonRegen_fixture_recovery.2.2.2.2.2.1] at h2
  rw [braytonRegen_fixture_recovery.2.2.2.2.2.2.2, braytonRegen_fixture_recovery.2.2.2.2.1] at h3
  exact ⟨h1, h2, h3⟩

-- No negative recovery at any turbine inlet temperature, for this compressor and regenerator.
example (T₃ : ℝ) :
    0 ≤ braytonRegenHeat 300 T₃ (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) :=
  braytonRegenHeat_nonneg (by norm_num) (by norm_num)

-- Positive recovery at the recovery fixture: the exhaust is hotter and `UA > 0`.
example : 0 < braytonRegenHeat 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) :=
  (braytonRegenHeat_pos_iff (by norm_num) (by norm_num)).mpr ⟨regen_recovery_lt, by norm_num⟩

-- The demand falls strictly at the recovery fixture and not at all at the bypass fixture.
example :
    braytonRegenHeatIn 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) <
        braytonLossyHeatIn 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) ∧
      ¬ braytonRegenHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) <
        braytonLossyHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) := by
  refine ⟨(braytonRegenHeatIn_le_braytonLossyHeatIn (by norm_num) (by norm_num)).2.mpr
    ⟨regen_recovery_lt, by norm_num⟩, fun h => ?_⟩
  have hlt := ((braytonRegenHeatIn_le_braytonLossyHeatIn (by norm_num) (by norm_num)).2.mp h).1
  exact absurd hlt (not_lt.mpr regen_bypass_lt.le)

-- At the recovery fixture the compressed stream ends between `750 K` and `900 K`, below the
-- exhaust inlet, and so does the exhaust, above the compressed-stream inlet.
example :
    (750 : ℝ) ≤
        braytonRegenPreheatTemp 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) ∧
      braytonRegenPreheatTemp 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) <
        900 ∧
      (750 : ℝ) <
        braytonRegenExhaustTemp 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) ∧
      braytonRegenExhaustTemp 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) ≤
        900 := by
  have h := braytonRegen_temp_order (UA := 6027 / 2) (by norm_num) (by norm_num)
    regen_recovery_lt
  rw [braytonRegen_fixture_recovery.1, braytonRegen_fixture_recovery.2.1] at h
  exact h

-- Both fixtures keep a positive external heat demand.
example :
    0 < braytonRegenHeatIn 300 1800 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) ∧
      0 < braytonRegenHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) := by
  refine ⟨braytonRegenHeatIn_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_, braytonRegenHeatIn_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_⟩
  · rw [braytonRegen_fixture_recovery.1]
    norm_num
  · rw [braytonRegen_fixture_bypass.1]
    norm_num

-- The closed-form counterflow solution between the recovery fixture's ports (`L = 1`) delivers
-- the regenerator outlets `1725/2 K` and `1575/2 K` and moves `452025/4 J/kg`.
example :
    counterflowColdTemp (2009 / 2) (2009 / 2) (6027 / 2 / 1) 1
        (braytonLossyExpandedTemp 1800 (2187 / 128) 287 (2009 / 2) (9 / 10))
        (braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6)) 0 = 1725 / 2 ∧
      counterflowHotTemp (2009 / 2) (2009 / 2) (6027 / 2 / 1) 1
        (braytonLossyExpandedTemp 1800 (2187 / 128) 287 (2009 / 2) (9 / 10))
        (braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6)) 1 = 1575 / 2 ∧
      2009 / 2 * (counterflowColdTemp (2009 / 2) (2009 / 2) (6027 / 2 / 1) 1
          (braytonLossyExpandedTemp 1800 (2187 / 128) 287 (2009 / 2) (9 / 10))
          (braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6)) 0 -
        braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6)) = 452025 / 4 := by
  have hsol := isCounterflowSolution_closedForm (Ch := 2009 / 2) (Cc := 2009 / 2)
    (K := 6027 / 2 / 1) (L := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (braytonLossyExpandedTemp 1800 (2187 / 128) 287 (2009 / 2) (9 / 10))
    (braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6))
  obtain ⟨h5, h6, hQ, -⟩ := braytonRegen_of_isCounterflowSolution (UA := 6027 / 2) (L := 1)
    (by norm_num) (by norm_num) (by norm_num) regen_recovery_lt hsol
  exact ⟨h5.trans braytonRegen_fixture_recovery.2.2.2.1,
    h6.trans braytonRegen_fixture_recovery.2.2.2.2.1,
    hQ.trans braytonRegen_fixture_recovery.2.2.2.2.2.1⟩

-- Connected against the gradient at the bypass fixture, the closed-form solution would cool the
-- compressed stream below `750 K` and heat the exhaust above `675 K`; the ports recover nothing.
example :
    counterflowColdTemp (2009 / 2) (2009 / 2) (6027 / 2 / 1) 1
        (braytonLossyExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) (9 / 10))
        (braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6)) 0 <
        braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6) ∧
      braytonLossyExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) (9 / 10) <
        counterflowHotTemp (2009 / 2) (2009 / 2) (6027 / 2 / 1) 1
          (braytonLossyExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) (9 / 10))
          (braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6)) 1 ∧
      braytonRegenHeat 300 1350 (2187 / 128) 287 (2009 / 2) (5 / 6) (9 / 10) (6027 / 2) = 0 := by
  have hsol := isCounterflowSolution_closedForm (Ch := 2009 / 2) (Cc := 2009 / 2)
    (K := 6027 / 2 / 1) (L := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (braytonLossyExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) (9 / 10))
    (braytonLossyCompressedTemp 300 (2187 / 128) 287 (2009 / 2) (5 / 6))
  exact braytonRegen_reversal_of_isCounterflowSolution (UA := 6027 / 2) (L := 1) (by norm_num)
    (by norm_num) (by norm_num) regen_bypass_lt hsol

end PhyslibExtTest.Thermodynamics.ExergyAndLosses
